//
// Created by yuhao on 2/20/24.
//

#ifndef SPECIFICATION_SPECIFICATION_H
#define SPECIFICATION_SPECIFICATION_H

#include "klee/Utils/llvm_related.h"
#include <cstdint>
#include <string>

namespace hy {

// yuhao: pointer and fields of struct have direction
enum Direction {
  DEFAULT = 0,
  IN,
  OUT,
  INOUT,
};

// yuhao: represent the value of a type in syzlang
class Value {
public:
  // yuhao: mode
  // -1. do not have constraints
  // 0. do not get value
  // 1. one const value (0x42),
  // 2. range (0:100),
  // 3. range with interval (1:10, 2) (todo)
  // 4. length of array
  int64_t mode = 0;
  uint64_t const_value;
  uint64_t min;
  uint64_t max;
  uint64_t interval;
  std::string name;

  void set_no_constraints() { mode = -1; }

  void set_const(uint64_t v) {
    mode = 1;
    const_value = v;
  }

  void set_range(uint64_t l, uint64_t r) {
    mode = 2;
    min = l;
    max = r;
  }

  void set_interval(uint64_t l, uint64_t r, uint64_t i) {
    mode = 3;
    min = l;
    max = r;
    interval = i;
  }
};

class Type {
public:
  llvm::Type::TypeID llvmTypeID;
  // yuhao: add a field to store the llvm type
  // it may not accurate
  llvm::Type *type = nullptr;

  bool is_opt = false;

  virtual ~Type(){};
  void set_type(llvm::Type *t) { type = t; }
};

class IntegerType : public Type {
public:
  uint64_t bit_width;
  Value value;

  IntegerType();
  virtual ~IntegerType(){};
};

class PointerType : public Type {
public:
  Type *element_type = nullptr;
  Direction direction = Direction::DEFAULT;

  PointerType();
  virtual ~PointerType() {
    if (element_type != nullptr) {
      delete element_type;
    }
  };

  uint64_t update_direction(Direction d);
};

// yuhao: for array type, we have two modes
// 1. one element type, size is optional
// 2. store all elements, size is fixed
// we use mode 1 for now
class ArrayType : public Type {
public:
  llvm::ArrayType *at = nullptr;

  // mode 1
  Type *element_type = nullptr;
  Value length;
  // mode 2
  std::vector<Type *> elements;

  ArrayType();
  virtual ~ArrayType() {
    if (element_type != nullptr) {
      delete element_type;
    }
    for (auto e : elements) {
      delete e;
    }
  }
};

class StructType : public Type {
public:
  llvm::StructType *st = nullptr;
  uint64_t id = 0;

  std::string name;
  std::vector<Type *> fields;
  bool is_packed = false;

  StructType();
  virtual ~StructType() {
    for (auto f : fields) {
      delete f;
    }
  }

  uint64_t get_id();
  uint64_t set_name(std::string n);
  std::string get_name();
};

} // namespace hy

#endif // SPECIFICATION_SPECIFICATION_H