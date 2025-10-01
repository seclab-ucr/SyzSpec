//
// Created by yuhao on 2/20/24.
//

#include "klee/Specification/Specification.h"

#include "klee/Utils/llvm_related.h"
#include "klee/Utils/log.h"
#include <cstdint>

namespace hy {

IntegerType::IntegerType() { llvmTypeID = llvm::Type::IntegerTyID; }

PointerType::PointerType() {
  llvmTypeID = llvm::Type::PointerTyID;
  direction = Direction::DEFAULT;
}

uint64_t PointerType::update_direction(Direction d) {
  uint64_t ret = 0;
  switch (direction) {
  case Direction::DEFAULT: {
    direction = d;
    break;
  }
  case Direction::IN: {
    if (d == Direction::OUT || d == Direction::INOUT) {
      direction = Direction::INOUT;
      ret = 8;
    }
    break;
  }
  case Direction::OUT: {
    if (direction == Direction::IN || d == Direction::INOUT) {
      direction = Direction::INOUT;
      ret = 8;
    }
    break;
  }
  case Direction::INOUT: {
    break;
  }
  default: {
    hy_log(3, "PointerType::update_direction(): " + std::to_string(d));
    break;
  }
  }
  return ret;
}

ArrayType::ArrayType() { llvmTypeID = llvm::Type::ArrayTyID; }

StructType::StructType() { llvmTypeID = llvm::Type::StructTyID; }

uint64_t StructType::get_id() {
  if (id == 0) {
    std::hash<std::string> str_hash;
    id = str_hash(get_name());
  }
  return id;
}

uint64_t StructType::set_name(std::string n) {
  std::string ret;
  for (auto temp : n) {
    if (temp == '.') {
      ret += '_';
    } else {
      ret += temp;
    }
  }
  name = ret;
  return 0;
}

std::string StructType::get_name() { return name; }

} // namespace hy