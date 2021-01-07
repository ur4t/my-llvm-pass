#include "llvm/ADT/StringRef.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <cstddef>
#include <random>
#include <vector>

#include "PluginVersion.h"

#define PLUGIN_NAME "str-obfs"
#define DEBUG_TYPE PLUGIN_NAME

using namespace llvm;

namespace {

cl::opt<unsigned> USER_SEED("seed", cl::init(0),
                            cl::desc("Use a seed to generate encryption key"),
                            cl::value_desc("non-zero unsigned int"));

enum {
  OBFS_CAESAR = 0,
  OBFS_XOR = 1,
};

cl::opt<int>
    OBFS_ALGO("obfs-algo", cl::init(OBFS_CAESAR),
              cl::desc("Algo to use:\n 0 - Caesar (default)\n 1 - Xor"));

struct EncodedVariable {
  GlobalVariable *gv;
  char key;
  size_t size;
  EncodedVariable(GlobalVariable *gv, char key, size_t size)
      : gv(gv), key(key), size(size) {}
};

template <typename ExtendType> struct ObfsAlgo {
  Function *decode_start = nullptr;
  std::vector<EncodedVariable> encoded_variables;

  static StringRef getEncodedString(const StringRef &str, char key) {
    const auto size = str.size();
    const auto *data = str.begin();
    auto *encoded = new char[size];
    for (auto i = 0; i < size; ++i) {
      encoded[i] = ExtendType::encoder(data[i], key);
    }
    return {encoded, size};
  }

  explicit ObfsAlgo(Module &mod) {
    std::random_device random_device;
    std::mt19937 engine(USER_SEED != 0 ? USER_SEED : random_device());
    std::uniform_int_distribution<unsigned char> distribution;
    auto &ctx = mod.getContext();

    //////////////////////////////////////////////////////////////////////////////

    // Encode all global strings
    for (auto &gv : mod.globals()) {
      auto key = char(distribution(engine));

      // Ignore external globals & uninitialized globals.
      if (!(gv.hasInitializer() && !gv.hasExternalLinkage() &&
            gv.getSection() != ".debug_gdb_scripts")) {
        continue;
      }

      Constant *initializer = gv.getInitializer();

      // Only support byte string, wide string support is platform dependent
      if (isa<ConstantDataArray>(initializer)) {
        auto *cda = cast<ConstantDataArray>(initializer);
        if (cda == nullptr || !cda->isString()) {
          continue;
        }

        auto encoded_str = getEncodedString(cda->getAsString(), key);

        // Override the constant with a new constant.
        gv.setInitializer(
            ConstantDataArray::getString(ctx, encoded_str, false));

        encoded_variables.emplace_back(&gv, key, encoded_str.size());
        gv.setConstant(false);
      }

      // Rust strings are constant structs:
      // - with only 1 operand.
      // - without trailing null byte.
      if (isa<ConstantStruct>(initializer)) {
        auto *cs = cast<ConstantStruct>(initializer);
        if (cs->getNumOperands() > 1) {
          continue;
        }

        auto *cda = cast<ConstantDataArray>(cs->getOperand(0));
        if (cda == nullptr || !cda->isString()) {
          continue;
        }

        auto encoded_str = getEncodedString(cda->getAsString(), key);

        cs->setOperand(0,
                       ConstantDataArray::getString(ctx, encoded_str, false));

        encoded_variables.emplace_back(&gv, key, encoded_str.size());
        gv.setConstant(false);
      }
    }

    //////////////////////////////////////////////////////////////////////////////

    // Add Decode function
    auto *decode_handle = cast<Function>(
        mod.getOrInsertFunction(
               /*Name=*/"__dec_handle." + std::to_string(distribution(engine)),
               FunctionType::get(
                   /*Result=*/Type::getVoidTy(ctx),
                   /*Params=*/
                   {Type::getInt8PtrTy(ctx, 8), Type::getInt8Ty(ctx),
                    Type::getInt64Ty(ctx)},
                   /*isVarArg=*/false))
            .getCallee());
    decode_handle->setCallingConv(CallingConv::C);

    // Name arguments
    auto *string_ptr = decode_handle->getArg(0);
    auto *key = decode_handle->getArg(1);
    auto *size = decode_handle->getArg(2);

    // Create blocks
    auto *entry = BasicBlock::Create(ctx, "entry", decode_handle);
    auto *loop = BasicBlock::Create(ctx, "loop", decode_handle);
    auto *end = BasicBlock::Create(ctx, "end", decode_handle);

    // Entry block
    IRBuilder<> builder(entry);
    auto *entry_encoded_byte = builder.CreateLoad(string_ptr);
    auto *entry_counter =
        builder.CreateSub(size, ConstantInt::get(IntegerType::get(ctx, 64), 1));
    builder.CreateBr(loop);

    // Decoding loop
    builder.SetInsertPoint(loop);
    auto *counter = builder.CreatePHI(Type::getInt64Ty(ctx), 2);
    auto *encoded_byte_ptr = builder.CreateGEP(string_ptr, counter);
    auto *encoded_byte = builder.CreateLoad(encoded_byte_ptr);

    auto *decoded_byte = ExtendType::decoder(builder, encoded_byte, key);
    builder.CreateStore(decoded_byte, encoded_byte_ptr);

    auto *next_counter = builder.CreateSub(
        counter, ConstantInt::get(IntegerType::get(ctx, 64), 1));

    auto *is_counter_zero = builder.CreateICmpEQ(
        counter, ConstantInt::get(IntegerType::get(ctx, 64), 0));
    builder.CreateCondBr(is_counter_zero, end, loop);

    counter->addIncoming(entry_counter, entry);
    counter->addIncoming(next_counter, loop);

    // End block
    builder.SetInsertPoint(end);
    builder.CreateRetVoid();

    //////////////////////////////////////////////////////////////////////////////

    // Add decode_stub function
    decode_start = cast<Function>(
        mod.getOrInsertFunction(/*Name=*/"__dec_start." +
                                    std::to_string(distribution(engine)),
                                FunctionType::get(
                                    /*Result=*/Type::getVoidTy(ctx),
                                    /*Params=*/{},
                                    /*isVarArg=*/false))
            .getCallee());
    decode_start->setCallingConv(CallingConv::C);

    // Create entry block
    IRBuilder<> stub_builder(BasicBlock::Create(ctx, "entry", decode_start));

    // Add calls to decode every encoded global
    for (auto &i : encoded_variables) {
      stub_builder.CreateCall(
          decode_handle,
          {stub_builder.CreatePointerCast(i.gv, Type::getInt8PtrTy(ctx, 8)),
           ConstantInt::get(Type::getInt8Ty(ctx), i.key),
           ConstantInt::get(Type::getInt64Ty(ctx), i.size)});
    }
    stub_builder.CreateRetVoid();
  }
};

struct ObfsXor : ObfsAlgo<ObfsXor> {
  static char encoder(char a, char b) { return char(a ^ b); }

  static Value *decoder(IRBuilder<> &builder, Value *encoded_byte, Value *key) {
    return builder.CreateXor(encoded_byte, key, "xor");
  }

  explicit ObfsXor(Module &M) : ObfsAlgo(M) {}
};

struct ObfsCaesar : ObfsAlgo<ObfsCaesar> {
  static char encoder(char a, char b) { return char(a + b); }

  static Value *decoder(IRBuilder<> &builder, Value *encoded_byte, Value *key) {
    return builder.CreateSub(encoded_byte, key, "sub");
  }

  explicit ObfsCaesar(Module &M) : ObfsAlgo(M) {}
};

bool runPass(Module &mod) {
  switch (OBFS_ALGO) {
  case OBFS_CAESAR:
    appendToGlobalCtors(mod, ObfsCaesar(mod).decode_start, 0);
    break;
  case OBFS_XOR:
    appendToGlobalCtors(mod, ObfsXor(mod).decode_start, 0);
    break;
  }
  return false;
};

// legacy pass for clang
struct LegacyStrObfsPass : public ModulePass {
  static char ID;
  LegacyStrObfsPass() : ModulePass(ID) {}
  bool runOnModule(Module &M) override { return runPass(M); }
};

char LegacyStrObfsPass::ID = 0;
RegisterPass<LegacyStrObfsPass> X(PLUGIN_NAME, PLUGIN_NAME,
                                  false /* Only looks at CFG */,
                                  false /* Analysis Pass */);

struct StrObfsPass : public PassInfoMixin<StrObfsPass> {
  static PreservedAnalyses run(Module &M, ModuleAnalysisManager & /*MAM*/) {
    if (!runPass(M)) {
      return PreservedAnalyses::all();
    }
    return PreservedAnalyses::none();
  };
};
} // end anonymous namespace

static llvm::RegisterStandardPasses RegisterStrObfsPass(
    llvm::PassManagerBuilder::EP_ModuleOptimizerEarly,
    [](const llvm::PassManagerBuilder & /*Builder*/,
       llvm::legacy::PassManagerBase &PM) { PM.add(new LegacyStrObfsPass()); });

static llvm::RegisterStandardPasses RegisterOpt0StrObfsPass(
    llvm::PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const llvm::PassManagerBuilder & /*Builder*/,
       llvm::legacy::PassManagerBase &PM) { PM.add(new LegacyStrObfsPass()); });

extern "C" llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, PLUGIN_NAME, PLUGIN_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement> /*ArrayRef*/) {
                  if (Name == PLUGIN_NAME) {
                    MPM.addPass(StrObfsPass());
                    return true;
                  }
                  return false;
                });
          }};
}
