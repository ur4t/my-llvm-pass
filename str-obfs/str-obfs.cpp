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
  EncodedVariable(GlobalVariable *gv, char key) : gv(gv), key(key) {}
};

template <typename ExtendType> struct ObfsAlgo {
  Function *decode_stub = nullptr;
  std::vector<EncodedVariable> EncodedVariables;

  static StringRef getEncodedString(const StringRef &str, char key) {
    auto size = str.size();
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
      if (!(gv.hasInitializer() && !gv.hasExternalLinkage()
            // &&
            // gv.getName().str().substr(0, 4) == ".str" && gv.isConstant() &&
            // isa<ConstantDataSequential>(gv.getInitializer()) &&
            // gv.getSection() != "llvm.metadata" &&
            // gv.getSection().find("__objc_methname") == std::string::npos &&
            // gv.getType()
            //     ->getArrayElementType()
            //     ->getArrayElementType()
            //     ->isIntegerTy()
            )) {
        continue;
      }

      Constant *initializer = gv.getInitializer();

      // Only support byte string
      // TODO: wide string support (wide char)
      // TODO: rust string support (constant struct)
      if (isa<ConstantDataArray>(initializer)) {
        auto *cda = cast<ConstantDataArray>(initializer);
        if (!cda->isString()) {
          continue;
        }

        // Override the constant with a new constant.
        gv.setInitializer(ConstantDataArray::getString(
            ctx, getEncodedString(cda->getAsString(), key), false));

        EncodedVariables.emplace_back(&gv, key);
        gv.setConstant(false);
      }
    }

    //////////////////////////////////////////////////////////////////////////////

    // Add Decode function
    auto *decoder = cast<Function>(
        mod.getOrInsertFunction(
               /*Name=*/"decoder",
               FunctionType::get(
                   /*Result=*/Type::getVoidTy(ctx),
                   /*Params=*/
                   {Type::getInt8PtrTy(ctx, 8), Type::getInt8Ty(ctx)},
                   /*isVarArg=*/false))
            .getCallee());
    decoder->setCallingConv(CallingConv::C);

    // Name DecodeFunc arguments
    auto *string_ptr = decoder->getArg(0);
    auto *key = decoder->getArg(1);

    // Create blocks
    auto *entry = BasicBlock::Create(ctx, "entry", decoder);
    auto *loop = BasicBlock::Create(ctx, "loop", decoder);
    auto *end = BasicBlock::Create(ctx, "end", decoder);

    // Entry block
    IRBuilder<> builder(entry);
    auto *entry_encoded_byte =
        builder.CreateLoad(string_ptr, "entry-encoded-byte");

    // It will always points to a valid encoded string, so no need for cond.
    builder.CreateBr(loop);
    // auto *isEntryEncodedByteNULL = builder.CreateICmpEQ(
    //     entryEncodedByte, Constant::getNullValue(Type::getInt8Ty(Ctx)),
    //     "cmp1");
    // builder.CreateCondBr(isEntryEncodedByteNULL, end, loop);

    // Decryption loop
    builder.SetInsertPoint(loop);
    auto *encoded_byte =
        builder.CreatePHI(Type::getInt8Ty(ctx), 2, "encoded-byte");
    auto *encoded_byte_ptr =
        builder.CreatePHI(Type::getInt8PtrTy(ctx, 8), 2, "encoded-byte-ptr");

    auto *decoded_byte = ExtendType::decoder(builder, encoded_byte, key);
    builder.CreateStore(decoded_byte, encoded_byte_ptr);

    auto *next_encoded_byte_ptr = builder.CreateGEP(
        encoded_byte_ptr, ConstantInt::get(IntegerType::get(ctx, 64), 1),
        "next-encoded-byte-ptr");
    auto *next_encoded_byte =
        builder.CreateLoad(next_encoded_byte_ptr, "next-encoded-byte");

    auto *is_decoded_byte_null = builder.CreateICmpEQ(
        decoded_byte, ConstantInt::get(IntegerType::get(ctx, 8), 0),
        "is-decoded-byte-null");

    builder.CreateCondBr(is_decoded_byte_null, end, loop);

    encoded_byte->addIncoming(entry_encoded_byte, entry);
    encoded_byte->addIncoming(next_encoded_byte, loop);
    encoded_byte_ptr->addIncoming(string_ptr, entry);
    encoded_byte_ptr->addIncoming(next_encoded_byte_ptr, loop);

    // End block
    builder.SetInsertPoint(end);
    builder.CreateRetVoid();

    //////////////////////////////////////////////////////////////////////////////

    // Add DecodeStub function
    decode_stub = cast<Function>(
        mod.getOrInsertFunction(/*Name=*/"decode_stub",
                                FunctionType::get(
                                    /*Result=*/Type::getVoidTy(ctx),
                                    /*Params=*/{},
                                    /*isVarArg=*/false))
            .getCallee());
    decode_stub->setCallingConv(CallingConv::C);

    // Create entry block
    IRBuilder<> stub_builder(BasicBlock::Create(ctx, "entry", decode_stub));

    // Add calls to decode every encoded global
    for (auto &var : EncodedVariables) {
      stub_builder.CreateCall(
          decoder,
          {stub_builder.CreatePointerCast(var.gv, Type::getInt8PtrTy(ctx, 8)),
           ConstantInt::get(Type::getInt8Ty(ctx), var.key)});
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
    appendToGlobalCtors(mod, ObfsCaesar(mod).decode_stub, 0);
    break;
  case OBFS_XOR:
    appendToGlobalCtors(mod, ObfsXor(mod).decode_stub, 0);
    break;
  }
  return false;
};

// legacy pass for clang
struct LegacyByteCaesarPass : public ModulePass {
  static char ID;
  LegacyByteCaesarPass() : ModulePass(ID) {}
  bool runOnModule(Module &M) override { return runPass(M); }
};

char LegacyByteCaesarPass::ID = 0;
RegisterPass<LegacyByteCaesarPass> X(PLUGIN_NAME, PLUGIN_NAME,
                                     false /* Only looks at CFG */,
                                     false /* Analysis Pass */);

struct ByteCaesarPass : public PassInfoMixin<ByteCaesarPass> {
  static PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM) {
    if (!runPass(M)) {
      return PreservedAnalyses::all();
    }
    return PreservedAnalyses::none();
  };
};
} // end anonymous namespace

static llvm::RegisterStandardPasses
    RegisterByteCaesarPass(llvm::PassManagerBuilder::EP_ModuleOptimizerEarly,
                           [](const llvm::PassManagerBuilder &Builder,
                              llvm::legacy::PassManagerBase &PM) {
                             PM.add(new LegacyByteCaesarPass());
                           });

static llvm::RegisterStandardPasses
    RegisterOpt0ByteCaesarPass(llvm::PassManagerBuilder::EP_EnabledOnOptLevel0,
                               [](const llvm::PassManagerBuilder &Builder,
                                  llvm::legacy::PassManagerBase &PM) {
                                 PM.add(new LegacyByteCaesarPass());
                               });

extern "C" llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, PLUGIN_NAME, PLUGIN_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement> ArrayRef) {
                  if (Name == PLUGIN_NAME) {
                    MPM.addPass(ByteCaesarPass());
                    return true;
                  }
                  return false;
                });
          }};
}
