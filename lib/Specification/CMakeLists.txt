#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_library(Linux
  Specification.cpp
  SpecificationConfig.cpp
  SpecificationManager.cpp
)

target_link_libraries(Linux PRIVATE ${ZLIB_LIBRARIES})

llvm_config(Linux "${USE_LLVM_SHARED}" support)
target_include_directories(Linux PRIVATE ${KLEE_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS})
target_compile_options(Linux PRIVATE ${KLEE_COMPONENT_CXX_FLAGS})
target_compile_definitions(Linux PRIVATE ${KLEE_COMPONENT_CXX_DEFINES})
