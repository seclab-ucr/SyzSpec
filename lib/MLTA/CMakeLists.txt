#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_library(MLTA
        Config.cc
        Common.cc
        Analyzer.cc
        CallGraph.cc
        MLTA.cc
        )

target_link_libraries(MLTA PRIVATE ${ZLIB_LIBRARIES})

llvm_config(MLTA "${USE_LLVM_SHARED}" support)
target_include_directories(MLTA PRIVATE ${KLEE_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS})
target_compile_options(MLTA PRIVATE ${KLEE_COMPONENT_CXX_FLAGS})
target_compile_definitions(MLTA PRIVATE ${KLEE_COMPONENT_CXX_DEFINES})
