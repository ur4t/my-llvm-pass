# Some pass plugins for llvm

## Compile
`cmake -Bbuild -DLLVM_INSTALL_DIR=/PATH/TO/LLVM_INSTALL_DIR`

## Usage

New pass manager style do not provide methods to handle commanline options, use legacy style instead.

### new pass manager style
`opt -load-pass-plugin=/PATH/TO/PLUGIN_NAME.so -passes="PLUGIN_NAME" -o OUTPUT TARGET.ll`

### legacy pass manager style
`opt -load /PATH/TO/PLUGIN_NAME.so -PLUGIN_NAME -o OUTPUT TARGET.ll`

### clang legacy pass manager style
`clang -Xclang -load -Xclang /PATH/TO/PLUGIN_NAME.so -o OUTPUT TARGET.c`