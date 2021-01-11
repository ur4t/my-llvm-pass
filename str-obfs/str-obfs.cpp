#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <random>

#include "PluginVersion.h"

#define PLUGIN_NAME "str-obfs"
#define DEBUG_TYPE PLUGIN_NAME

namespace {

using namespace llvm;

const unsigned int PASS_PRIORITY = 0;

cl::opt<bool, true> Debug("debug", cl::desc("Enable debug output"),
                          cl::location(DebugFlag));

cl::opt<unsigned> UserSeed("seed", cl::init(0),
                           cl::desc("Use a seed to generate encryption key"),
                           cl::value_desc("non-zero unsigned int"));

enum {
  ADD_CIPHER = 0,
  XOR_CIPHER = 1,
};

cl::opt<int>
    CipherType("cipher-type", cl::init(ADD_CIPHER),
               cl::desc("Algo to use:\n 0 - Caesar (default)\n 1 - Xor"));

struct EncodedVariable {
  GlobalVariable *gv;
  char key;
  size_t size;
  EncodedVariable(GlobalVariable *gv, char key, size_t size)
      : gv(gv), key(key), size(size) {}
};

struct Cipher {
  std::function<char(char, char)> encoder;
  std::function<Value *(IRBuilder<> &, Value *, Value *)> decoder;
};

Cipher Add{
    .encoder = [](char a, char b) { return char(a + b); },
    .decoder =
        [](IRBuilder<> &builder, Value *encoded_byte, Value *key) {
          return builder.CreateSub(encoded_byte, key, "sub");
        },
};

Cipher Xor{
    .encoder = [](char a, char b) { return char(a ^ b); },
    .decoder =
        [](IRBuilder<> &builder, Value *encoded_byte, Value *key) {
          return builder.CreateXor(encoded_byte, key, "xor");
        },
};

Function *getCtor(Module &mod, Cipher &cipher) {
  std::random_device random_device;
  std::mt19937 engine(UserSeed != 0 ? UserSeed : random_device());
  std::uniform_int_distribution<unsigned> distribution;
  Function *decode_handle;
  Function *decode_start;
  std::vector<EncodedVariable> encoded_variables;

  auto &ctx = mod.getContext();

  { // Encode all global strings
    for (auto &gv : mod.globals()) {
      auto key = char(distribution(engine));

      if (!gv.hasInitializer() || !gv.hasLocalLinkage()) {
        continue;
      }

      Constant *initializer = gv.getInitializer();

      // Only support byte strings, wide string support is platform dependent
      // A byte strings is a constant data array with trailing null byte.
      if (isa<ConstantDataArray>(initializer)) {
        auto *cda = cast<ConstantDataArray>(initializer);
        if (!cda->isString()) {
          continue;
        }
        auto str = cda->getAsString();
        auto size = str.size();
        auto *new_data = new char[size];
        for (auto i = 0; i < size; ++i) {
          new_data[i] = cipher.encoder(str[i], key);
        }
        gv.setInitializer(
            ConstantDataArray::getString(ctx, {new_data, size}, false));
        encoded_variables.emplace_back(&gv, key, size);
        gv.setConstant(false);
      }

      // Rust strings are constant structs with only 1 operand.
      // The operand is a constant data array without trailing null byte.
      if (isa<ConstantStruct>(initializer)) {
        auto *cs = cast<ConstantStruct>(initializer);
        if (cs->getNumOperands() > 1 ||
            !isa<ConstantDataArray>(cs->getOperand(0))) {
          continue;
        }
        auto *cda = cast<ConstantDataArray>(cs->getOperand(0));
        if (!cda->isString()) {
          continue;
        }
        auto str = cda->getAsString();
        auto size = str.size();
        auto *new_data = new char[size];
        for (auto i = 0; i < size; ++i) {
          new_data[i] = cipher.encoder(str[i], key);
        }
        cs->setOperand(
            0, ConstantDataArray::getString(ctx, {new_data, size}, false));
        encoded_variables.emplace_back(&gv, key, size);
        gv.setConstant(false);
      }
    }
  }

  { // Add Decode function
    decode_handle = cast<Function>(
        mod.getOrInsertFunction(
               "__dec_handle." + std::to_string(distribution(engine)),
               FunctionType::get(Type::getVoidTy(ctx),
                                 {Type::getInt8PtrTy(ctx), Type::getInt8Ty(ctx),
                                  Type::getInt64Ty(ctx)},
                                 false))
            .getCallee());

    // Name arguments
    auto *string_ptr = decode_handle->getArg(0);
    auto *key = decode_handle->getArg(1);
    auto *size = decode_handle->getArg(2);

    // Create blocks
    auto *entry = BasicBlock::Create(ctx, "entry", decode_handle);
    auto *loop = BasicBlock::Create(ctx, "loop", decode_handle);
    auto *end = BasicBlock::Create(ctx, "end", decode_handle);

    // Entry block
    IRBuilder<> irb(entry);
    auto *entry_encoded_byte = irb.CreateLoad(string_ptr);
    auto *entry_counter =
        irb.CreateSub(size, ConstantInt::get(Type::getInt64Ty(ctx), 1));
    irb.CreateBr(loop);

    // Decoding loop
    irb.SetInsertPoint(loop);
    auto *counter = irb.CreatePHI(Type::getInt64Ty(ctx), 2);
    auto *next_counter =
        irb.CreateSub(counter, ConstantInt::get(Type::getInt64Ty(ctx), 1));
    counter->addIncoming(entry_counter, entry);
    counter->addIncoming(next_counter, loop);

    auto *byte_ptr = irb.CreateGEP(string_ptr, counter);
    auto *encoded_byte = irb.CreateLoad(byte_ptr);
    auto *decoded_byte = cipher.decoder(irb, encoded_byte, key);
    irb.CreateStore(decoded_byte, byte_ptr);

    auto *is_counter_zero =
        irb.CreateICmpEQ(counter, ConstantInt::get(Type::getInt64Ty(ctx), 0));
    irb.CreateCondBr(is_counter_zero, end, loop);

    // End block
    irb.SetInsertPoint(end);
    LLVM_DEBUG({
      irb.CreateCall(
          mod.getOrInsertFunction(
              "write",
              FunctionType::get(Type::getInt64Ty(ctx),
                                {Type::getInt64Ty(ctx), Type::getInt8PtrTy(ctx),
                                 Type::getInt64Ty(ctx)},
                                false)),
          {ConstantInt::get(Type::getInt64Ty(ctx), 2), string_ptr, size});
      irb.CreateCall(
          mod.getOrInsertFunction(
              "puts", FunctionType::get(Type::getVoidTy(ctx),
                                        {Type::getInt8PtrTy(ctx)}, false)),
          {irb.CreateGlobalStringPtr("")});
    });
    irb.CreateRetVoid();
  }

  { // Add decode_stub function
    decode_start = cast<Function>(
        mod.getOrInsertFunction(
               "__dec_start." + std::to_string(distribution(engine)),
               FunctionType::get(Type::getVoidTy(ctx), {}, false))
            .getCallee());

    IRBuilder<> irb(BasicBlock::Create(ctx, "entry", decode_start));
    for (auto &i : encoded_variables) {
      irb.CreateCall(decode_handle,
                     {irb.CreatePointerCast(i.gv, Type::getInt8PtrTy(ctx)),
                      ConstantInt::get(Type::getInt8Ty(ctx), i.key),
                      ConstantInt::get(Type::getInt64Ty(ctx), i.size)});
    }
    LLVM_DEBUG({
      irb.CreateCall(
          mod.getOrInsertFunction(
              "puts", FunctionType::get(Type::getVoidTy(ctx),
                                        {Type::getInt8PtrTy(ctx)}, false)),
          {irb.CreateGlobalStringPtr("Decoded all strings!")});
    });
    irb.CreateRetVoid();
  }
  return decode_start;
}

bool runPass(Module &mod) {
  Cipher cipher;
  switch (CipherType) {
  case ADD_CIPHER:
    cipher = Add;
    break;
  case XOR_CIPHER:
    cipher = Xor;
    break;
  }
  appendToGlobalCtors(mod, getCtor(mod, Add), PASS_PRIORITY);
  return false;
};

// legacy pass for clang
struct LegacyPass : public ModulePass {
  static char ID;
  LegacyPass() : ModulePass(ID) {}
  bool runOnModule(Module &M) override { return runPass(M); }
};

char LegacyPass::ID = 0;
RegisterPass<LegacyPass> X(PLUGIN_NAME, PLUGIN_NAME,
                           false /* Only looks at CFG */,
                           false /* Analysis Pass */);

struct NewPass : public PassInfoMixin<NewPass> {
  static PreservedAnalyses run(Module &M, ModuleAnalysisManager & /*MAM*/) {
    if (!runPass(M)) {
      return PreservedAnalyses::all();
    }
    return PreservedAnalyses::none();
  };
};

llvm::RegisterStandardPasses RegisterPass(
    llvm::PassManagerBuilder::EP_ModuleOptimizerEarly,
    [](const llvm::PassManagerBuilder & /*unused*/,
       llvm::legacy::PassManagerBase &PM) { PM.add(new LegacyPass()); });

llvm::RegisterStandardPasses RegisterOpt0Pass(
    llvm::PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const llvm::PassManagerBuilder & /*unused*/,
       llvm::legacy::PassManagerBase &PM) { PM.add(new LegacyPass()); });

extern "C" llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, PLUGIN_NAME, PLUGIN_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement> /*unused*/) {
                  if (Name == PLUGIN_NAME) {
                    MPM.addPass(NewPass());
                    return true;
                  }
                  return false;
                });
          }};
}

} // end anonymous namespace
