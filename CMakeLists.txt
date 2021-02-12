cmake_minimum_required(VERSION 3.17)

project(my-obfs
        VERSION "0.1.0"
        )

set(CMAKE_CXX_STANDARD 14)

function(dump_variables)
    foreach(var ${ARGN})
        message(STATUS "${var} = ${${var}}")
    endforeach()
endfunction()

if(LLVM_INSTALL_DIR)
    list(APPEND CMAKE_PREFIX_PATH "${LLVM_INSTALL_DIR}/lib/cmake/llvm/")
endif()

find_package(LLVM 10...11 REQUIRED CONFIG)

dump_variables(
        LLVM_PACKAGE_VERSION
        LLVM_DEFINITIONS
        LLVM_CMAKE_DIR
        LLVM_INCLUDE_DIRS
        LLVM_LIBRARY_DIRS
        )

list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")

# CMake Modules used for llvm specific macros
include(LLVM-Config)
include(HandleLLVMOptions)
include(AddLLVM)

include_directories(${LLVM_INCLUDE_DIRS} ${PROJECT_BINARY_DIR})
link_directories(${LLVM_LIBRARY_DIRS})
add_definitions(${LLVM_DEFINITIONS})

configure_file(version.h.in PluginVersion.h)

add_subdirectory(str-obfs)
