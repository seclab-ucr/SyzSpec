//
// Created by yuhao on 7/20/24.
//

#ifndef SPECIFICATION_SPECIFICATIONMANAGER_H
#define SPECIFICATION_SPECIFICATIONMANAGER_H

#include "klee/Specification/Specification.h"
#include "klee/Specification/SpecificationConfig.h"

#include "klee/Utils/llvm_related.h"
#include "klee/Utils/log.h"

namespace hy {

class Specification {
public:
  uint64_t id;
  std::vector<Type *> args;

  virtual ~Specification() {
    for (auto arg : args) {
      delete arg;
    }
  }
  uint64_t add(Type *ty);
};

class SpecificationManager {
public:
  // yuhao: key: state id
  std::map<uint64_t, Specification *> specs;

  // yuhao: key: struct id
  std::map<uint64_t, StructType *> struct_types;

  SpecificationConfig *spec_config;

  uint64_t id = 0;
  std::string work_dir;

  SpecificationManager();

  uint64_t compare_spec(Specification *spec_1, Specification *spec_2);

  uint64_t compare_type(Type *ty_1, Type *ty_2);

  uint64_t merge(uint64_t id, Specification *spec);

  // yuhao: merge spec_2 into spec_1
  uint64_t merge_spec(Specification *spec_1, Specification *spec_2);

  // yuhao: merge ty_2 into ty_1
  uint64_t merge_type(Type *ty_1, Type *ty_2);

  // yuhao: merge val_2 into val_1
  uint64_t merge_value(Value *val_1, Value *val_2);

  uint64_t add_spec(uint64_t id, Specification *spec);

  uint64_t pre_process(Type *ty);

  uint64_t post_process(Type *ty);

  std::string to_sign(Type *ty, bool is_root = false);

  std::string to_syzlang();

  std::string to_syzlang(Specification *spec);

  std::string to_syzlang(Type *ty, Direction d = Direction::DEFAULT, bool is_root = true);

  std::string to_syzlang_with_fields(StructType *sty);

  std::string to_syzlang(Value *val, bool is_root = false);
};

// yuhao: check if a field of struct is optional
// when the field is the same as the struct itself, it is optional
bool is_opt_pointer(llvm::StructType *st, std::set<llvm::Type *> &checked,
                    llvm::Type *t);

} // namespace hy

#endif // SPECIFICATION_SPECIFICATIONMANAGER_H
