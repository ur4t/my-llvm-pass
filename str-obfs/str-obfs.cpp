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

cl::opt<unsigned> UserSeed("seed", cl::init(0),
                           cl::desc("Use a seed to generate encryption key"),
                           cl::value_desc("non-zero unsigned int"));

enum {
  CAESAR_CIPHER = 0,
  XOR_CIPHER = 1,
};

cl::opt<int>
    CipherType("cipher-type", cl::init(CAESAR_CIPHER),
               cl::desc("Algo to use:\n 0 - Caesar (default)\n 1 - Xor"));

struct EncodedVariable {
  GlobalVariable *gv;
  char key;
  size_t size;
  EncodedVariable(GlobalVariable *gv, char key, size_t size)
      : gv(gv), key(key), size(size) {}
};

template <typename Algorithm> struct Cipher {
  Function *decode_start = nullptr;
  std::vector<EncodedVariable> encoded_variables;

  static StringRef getEncodedString(const StringRef &str, char key) {
    const auto size = str.size();
    const auto *data = str.begin();
    auto *encoded = new char[size];
    for (auto i = 0; i < size; ++i) {
      encoded[i] = Algorithm::encoder(data[i], key);
    }
    return {encoded, size};
  }

  explicit Cipher(Module &mod) {
    std::random_device random_device;
    std::mt19937 engine(UserSeed != 0 ? UserSeed : random_device());
    std::uniform_int_distribution<unsigned char> distribution;
    auto &ctx = mod.getContext();
    Function *decode_handle;

    { // Encode all global strings
      for (auto &gv : mod.globals()) {
        auto key = char(distribution(engine));

        // Ignore:
        // - uninitialized globals,
        // - external globals,
        // - gdb script loaders.
        if (!gv.hasInitializer() || gv.hasExternalLinkage() ||
            gv.getSection() == ".debug_gdb_scripts") {
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

          auto encoded_str = getEncodedString(cda->getAsString(), key);
          gv.setInitializer(
              ConstantDataArray::getString(ctx, encoded_str, false));
          encoded_variables.emplace_back(&gv, key, encoded_str.size());
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

          auto encoded_str = getEncodedString(cda->getAsString(), key);
          cs->setOperand(0,
                         ConstantDataArray::getString(ctx, encoded_str, false));
          encoded_variables.emplace_back(&gv, key, encoded_str.size());
          gv.setConstant(false);
        }
      }
    }

    { // Add Decode function
      decode_handle = cast<Function>(
          mod.getOrInsertFunction(
                 /*Name=*/"__dec_handle." +
                     std::to_string(distribution(engine)),
                 FunctionType::get(
                     /*Result=*/Type::getVoidTy(ctx),
                     /*Params=*/
                     {Type::getInt8PtrTy(ctx), Type::getInt8Ty(ctx),
                      Type::getInt64Ty(ctx)},
                     /*isVarArg=*/false))
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
      auto *decoded_byte = Algorithm::decoder(irb, encoded_byte, key);
      irb.CreateStore(decoded_byte, byte_ptr);

      auto *is_counter_zero =
          irb.CreateICmpEQ(counter, ConstantInt::get(Type::getInt64Ty(ctx), 0));
      irb.CreateCondBr(is_counter_zero, end, loop);

      // End block
      irb.SetInsertPoint(end);
      irb.CreateRetVoid();
    }

    { // Add decode_stub function
      decode_start = cast<Function>(
          mod.getOrInsertFunction(/*Name=*/"__dec_start." +
                                      std::to_string(distribution(engine)),
                                  FunctionType::get(
                                      /*Result=*/Type::getVoidTy(ctx),
                                      /*Params=*/{},
                                      /*isVarArg=*/false))
              .getCallee());

      IRBuilder<> irb(BasicBlock::Create(ctx, "entry", decode_start));
      for (auto &i : encoded_variables) {
        irb.CreateCall(decode_handle,
                       {irb.CreatePointerCast(i.gv, Type::getInt8PtrTy(ctx)),
                        ConstantInt::get(Type::getInt8Ty(ctx), i.key),
                        ConstantInt::get(Type::getInt64Ty(ctx), i.size)});
      }
      irb.CreateRetVoid();
    }
  }
};

struct XorCipher : Cipher<XorCipher> {
  static char encoder(char a, char b) { return char(a ^ b); }

  static Value *decoder(IRBuilder<> &builder, Value *encoded_byte, Value *key) {
    return builder.CreateXor(encoded_byte, key, "xor");
  }

  explicit XorCipher(Module &M) : Cipher(M) {}
};

struct CaesarCipher : Cipher<CaesarCipher> {
  static char encoder(char a, char b) { return char(a + b); }

  static Value *decoder(IRBuilder<> &builder, Value *encoded_byte, Value *key) {
    return builder.CreateSub(encoded_byte, key, "sub");
  }

  explicit CaesarCipher(Module &M) : Cipher(M) {}
};

bool runPass(Module &mod) {
  switch (CipherType) {
  case CAESAR_CIPHER:
    appendToGlobalCtors(mod, CaesarCipher(mod).decode_start, PASS_PRIORITY);
    break;
  case XOR_CIPHER:
    appendToGlobalCtors(mod, XorCipher(mod).decode_start, PASS_PRIORITY);
    break;
  }
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
    [](const llvm::PassManagerBuilder & /*Builder*/,
       llvm::legacy::PassManagerBase &PM) { PM.add(new LegacyPass()); });

llvm::RegisterStandardPasses RegisterOpt0Pass(
    llvm::PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const llvm::PassManagerBuilder & /*Builder*/,
       llvm::legacy::PassManagerBase &PM) { PM.add(new LegacyPass()); });

extern "C" llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, PLUGIN_NAME, PLUGIN_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement> /*ArrayRef*/) {
                  if (Name == PLUGIN_NAME) {
                    MPM.addPass(NewPass());
                    return true;
                  }
                  return false;
                });
          }};
}

} // end anonymous namespace
