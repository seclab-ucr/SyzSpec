//
// Created by yuhao on 7/20/24.
//

#include "klee/Specification/SpecificationManager.h"
#include "klee/Specification/Specification.h"
#include "klee/Utils/log.h"

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <random>

namespace hy {

uint64_t Specification::add(Type *ty) {
  if (ty != nullptr) {
    args.push_back(ty);
  }
  return 0;
}

SpecificationManager::SpecificationManager() {

  // Get the current time as a seed
  auto seed = std::chrono::system_clock::now().time_since_epoch().count();

  // Initialize the random number generator with the seed
  std::mt19937 generator(seed);

  // Define the distribution for the full range of int
  std::uniform_int_distribution<int> distribution(
      std::numeric_limits<int>::min(), std::numeric_limits<int>::max());

  // Generate a random number
  id = distribution(generator);

  work_dir = std::filesystem::current_path();
}

// yuhao: compare two specifications
// return 0 if they are the same
// return 3 if the difference is determinate
uint64_t SpecificationManager::compare_spec(Specification *spec_1,
                                            Specification *spec_2) {
  // uint64_t debug = 1;
  uint64_t ret = 0;

  // yuhao: compare the number of arguments
  if (spec_1->args.size() != spec_2->args.size()) {
    ret = 3;
    return ret;
  }

  uint64_t size = spec_1->args.size();
  for (uint64_t i = 0; i < size; i++) {
    ret += compare_type(spec_1->args[i], spec_2->args[i]);
  }

  return ret;
}

uint64_t SpecificationManager::compare_type(Type *ty_1, Type *ty_2) {

  if (ty_1->llvmTypeID > ty_2->llvmTypeID) {
    auto temp = ty_1;
    ty_1 = ty_2;
    ty_2 = temp;
  }

  // yuhao: compare the type of the argument
  // if they are not the same, return 2
  // unless one is int64 and another is pointer
  if (ty_1->llvmTypeID != ty_2->llvmTypeID) {
    if (ty_1->llvmTypeID == llvm::Type::IntegerTyID &&
        ty_2->llvmTypeID == llvm::Type::PointerTyID) {
      auto ity = (IntegerType *)ty_1;
      if (ity->bit_width == 64 &&
          (ity->value.mode == -1 || ity->value.mode == 0)) {
        return 0;
      }
    }
    return 3;
  }

  std::string sign_1 = to_sign(ty_1, true);
  std::string sign_2 = to_sign(ty_2, true);

  if (sign_1 != sign_2) {
    return 3;
  }

  if (ty_1->llvmTypeID == llvm::Type::IntegerTyID) {
    auto ity_1 = (IntegerType *)ty_1;
    auto ity_2 = (IntegerType *)ty_2;

    if (ity_1->value.mode != ity_2->value.mode) {
      return 1;
    }

    if (ity_1->value.mode == 1) {
      if (ity_1->value.const_value != ity_2->value.const_value) {
        return 3;
      }
    }

    if (ity_1->value.mode == 2) {
      if (ity_1->value.min != ity_2->value.min ||
          ity_1->value.max != ity_2->value.max) {
        return 3;
      }
    }

    if (ity_1->value.mode == 3) {
      if (ity_1->value.min != ity_2->value.min ||
          ity_1->value.max != ity_2->value.max ||
          ity_1->value.interval != ity_2->value.interval) {
        return 3;
      }
    }
  }

  return 0;
}

uint64_t SpecificationManager::merge(uint64_t id, Specification *spec) {

  uint64_t ret = 0;

  if (specs.find(id) != specs.end()) {
    ret = merge_spec(specs[id], spec);
    return ret;
  }

  Specification *temp = nullptr;
  for (auto s : specs) {
    if (compare_spec(s.second, spec) == 0) {
      temp = s.second;
      break;
    }
  }
  if (temp != nullptr) {
    ret = merge_spec(temp, spec);
    return ret;
  }

  specs[id] = spec;
  ret = 32;
  return ret;
}

// yuhao: merge two specifications
// assume that the two specifications are the same
uint64_t SpecificationManager::merge_spec(Specification *spec_1,
                                          Specification *spec_2) {
  uint64_t debug = -1;
  uint64_t ret = 0;

  for (uint64_t i = 0; i < spec_1->args.size(); i++) {
    hy_log(debug, "before merge: \n" + to_syzlang(spec_1->args[i]) + "\n" +
                      to_syzlang(spec_2->args[i]));

    auto ty_1 = spec_1->args[i];
    auto ty_2 = spec_2->args[i];

    if (spec_1->args[i]->llvmTypeID == llvm::Type::IntegerTyID &&
        spec_2->args[i]->llvmTypeID == llvm::Type::PointerTyID) {
      ty_1 = spec_2->args[i];
      ty_2 = spec_1->args[i];
      spec_1->args[i] = ty_1;
      spec_2->args[i] = ty_2;
      ret += 8;
    }

    ret += merge_type(ty_1, ty_2);
    hy_log(debug, "after merge: \n" + to_syzlang(spec_1->args[i]));
  }

  delete spec_2;

  return ret;
}

// yuhao: merge two types
// assume that the two types are the same
// return 0 if there is no difference
uint64_t SpecificationManager::merge_type(Type *ty_1, Type *ty_2) {

  uint64_t debug = -1;

  uint64_t ret = 0;

  if (ty_1 == nullptr || ty_2 == nullptr) {
    return 0;
  }

  switch (ty_1->llvmTypeID) {
  case llvm::Type::IntegerTyID: {
    auto ity_1 = (IntegerType *)ty_1;

    switch (ty_2->llvmTypeID) {
    case llvm::Type::IntegerTyID: {
      auto ity_2 = (IntegerType *)ty_2;
      ret += merge_value(&ity_1->value, &ity_2->value);
      break;
    }
    case llvm::Type::PointerTyID: {
      hy_log(3, "SpecificationManager::compare(): " +
                    std::to_string(ty_1->llvmTypeID) + " " +
                    std::to_string(ty_2->llvmTypeID));
      break;
    }
    default: {
      break;
    }
    }
    break;
  }
  case llvm::Type::PointerTyID: {
    auto pty_1 = (PointerType *)ty_1;

    switch (ty_2->llvmTypeID) {
    case llvm::Type::IntegerTyID: {
      break;
    }
    case llvm::Type::PointerTyID: {
      auto pty_2 = (PointerType *)ty_2;
      ret += pty_1->update_direction(pty_2->direction);
      ret += merge_type(pty_1->element_type, pty_2->element_type);
      break;
    }
    default: {
      break;
    }
    }
    break;
  }
  case llvm::Type::ArrayTyID: {
    hy_log(debug, "aty_1: " + to_syzlang(ty_1));
    hy_log(debug, "aty_2: " + to_syzlang(ty_2));

    auto aty_1 = (ArrayType *)ty_1;
    auto aty_2 = (ArrayType *)ty_2;
    merge_value(&aty_1->length, &aty_2->length);

    break;
  }
  case llvm::Type::StructTyID: {
    auto sty_1 = (StructType *)ty_1;
    auto sty_2 = (StructType *)ty_2;

    hy_log(debug, "sty_1 field: \n" + to_syzlang_with_fields(sty_1));
    hy_log(debug, "sty_2 field: \n" + to_syzlang_with_fields(sty_2));

    if (to_sign(sty_1) == to_sign(sty_2)) {
      for (uint64_t i = 0; i < sty_1->fields.size(); i++) {
        ret += merge_type(sty_1->fields[i], sty_2->fields[i]);
      }
    } else {
      sty_1->id = sty_2->id;
      sty_1->set_name(sty_2->get_name());
      sty_1->fields.swap(sty_2->fields);
    }

    hy_log(debug, "after sty_1 field: \n" + to_syzlang_with_fields(sty_1));
    break;
  }
  default: {
    hy_log(3, "SpecificationManager::compare(): " +
                  std::to_string(ty_1->llvmTypeID));
    break;
  }
  }
  return ret;
}

// yuhao: merge two values
// return 0 if there is no difference
// assume that val_1 has <= model
uint64_t SpecificationManager::merge_value(Value *val_1, Value *val_2) {
  uint64_t ret = 0;
  if (val_1->mode == -1) {

    if (val_2->mode != -1) {
      val_1->mode = val_2->mode;
      val_1->const_value = val_2->const_value;
      val_1->min = val_2->min;
      val_1->max = val_2->max;
      val_1->interval = val_2->interval;
      val_1->name = val_2->name;
      ret = 1;
    }

  } else if (val_1->mode == 0) {
    if (val_2->mode == 4) {
      val_1->mode = val_2->mode;
      val_1->name = val_2->name;
      ret = 1;
    }

  } else if (val_1->mode == 1) {

    if (val_2->mode == -1) {

    } else if (val_2->mode == 0) {
      val_1->mode = val_2->mode;
      ret = 1;

    } else if (val_2->mode == 1) {
      if (val_1->const_value != val_2->const_value) {
        val_1->mode = 2;
        val_1->min = val_1->const_value;
        val_1->max = val_1->const_value;
        if (val_1->min > val_2->const_value) {
          val_1->min = val_2->const_value;
        } else {
          val_1->max = val_2->const_value;
        }
        ret = 1;
      }

    } else if (val_2->mode == 2) {
      val_1->mode = 2;
      val_1->min = val_2->min;
      val_1->max = val_2->max;
      if (val_1->min > val_1->const_value) {
        val_1->min = val_1->const_value;
      } else if (val_1->max < val_1->const_value) {
        val_1->max = val_1->const_value;
      }
      val_1->const_value = val_2->const_value;
      ret = 1;

    } else if (val_2->mode == 3) {
      hy_log(3, "unspport mode 3");
    } else if (val_2->mode == 4) {
      val_1->mode = val_2->mode;
      val_1->name = val_2->name;
      ret = 1;
    }
  } else if (val_1->mode == 2) {

    if (val_2->mode == -1) {

    } else if (val_2->mode == 0) {
      val_1->mode = val_2->mode;
      ret = 1;

    } else if (val_2->mode == 1) {

      if (val_1->min > val_2->const_value) {
        val_1->min = val_2->const_value;
        ret = 1;
      } else if (val_1->max < val_2->const_value) {
        val_1->max = val_2->const_value;
        ret = 1;
      }

    } else if (val_2->mode == 2) {

      if (val_1->min > val_2->min) {
        val_1->min = val_2->min;
        ret += 1;
      }
      if (val_1->max < val_2->max) {
        val_1->max = val_2->max;
        ret += 1;
      }

    } else if (val_2->mode == 3) {
      hy_log(3, "unspport mode 3");
    } else if (val_2->mode == 4) {
      val_1->mode = val_2->mode;
      val_1->name = val_2->name;
      ret = 1;
    }
  } else if (val_1->mode == 3) {
    hy_log(3, "unspport mode 3");
  } else if (val_1->mode == 4) {
  }
  return ret;
}

uint64_t SpecificationManager::add_spec(uint64_t id, Specification *spec) {

  uint64_t debug = -1;
  uint64_t ret = 0;
  // yuhao: pre process the spec
  for (auto arg : spec->args) {
    pre_process(arg);
  }

  hy_log(debug,
         "add_spec: state id: " + std::to_string(id) + "\n" + to_syzlang(spec));

  ret = merge(id, spec);

  struct_types.clear();
  for (auto s : specs) {
    for (auto arg : s.second->args) {
      post_process(arg);
    }
  }

  hy_log(debug, "ret: " + std::to_string(ret));
  hy_log(debug, "spec: \n" + to_syzlang());

  return ret;
}

// yuhao: set the name of the struct type
uint64_t SpecificationManager::pre_process(Type *ty) {

  if (ty == nullptr) {
    return 0;
  }

  switch (ty->llvmTypeID) {
  case llvm::Type::IntegerTyID: {
    break;
  }
  case llvm::Type::PointerTyID: {
    pre_process(((PointerType *)ty)->element_type);
    break;
  }
  case llvm::Type::ArrayTyID: {
    break;
  }
  case llvm::Type::StructTyID: {

    auto sty = (StructType *)ty;

    // yuhao: handle the len of the array
    for (auto field : sty->fields) {
      if (field->llvmTypeID != llvm::Type::IntegerTyID) {
        continue;
      }

      auto ity = (IntegerType *)field;
      uint64_t len = 0;
      if (ity->value.mode == 1) {
        len = ity->value.const_value;
      } else if (ity->value.mode == 2) {
        len = ity->value.min;
      } else {
        continue;
      }

      if (len == 0) {
        continue;
      }

      int64_t field_index = -1;
      for (auto another_field : sty->fields) {
        field_index++;
        if (another_field->llvmTypeID != llvm::Type::PointerTyID) {
          continue;
        }

        auto pty = (PointerType *)another_field;
        if (pty->element_type == nullptr) {
          continue;
        }
        if (pty->element_type->llvmTypeID != llvm::Type::ArrayTyID) {
          continue;
        }

        auto aty = (ArrayType *)pty->element_type;
        if (aty->length.mode == 1) {
          if (aty->length.const_value == len) {
            aty->length.mode = 0;
            ity->value.mode = 4;
            ity->value.name = "field_" + std::to_string(field_index);
          }
        }
      }
    }

    for (auto field : sty->fields) {
      pre_process(field);
    }

    // yuhao: set the name of the struct type
    std::string name = sty->get_name();
    if (name.empty()) {
      std::string temp_name;

      if (sty->st == nullptr) {
        temp_name = "struct_";
      } else {
        temp_name = sty->st->getStructName().str() + "_";
      }

      std::string temp;
      for (uint64_t i = 0; i < sty->fields.size(); i++) {
        bool is_root = false;
        if (sty->st == nullptr) {
          if (i == sty->fields.size() - 1) {
            is_root = true;
          }
        } else if (sty->st != nullptr) {
          if (sty->fields[i]->llvmTypeID == llvm::Type::PointerTyID) {
            auto pty = (PointerType *)sty->fields[i];
            if (pty->element_type != nullptr &&
                pty->element_type->llvmTypeID == llvm::Type::ArrayTyID) {
              is_root = true;
            }
          }
        }
        temp += to_sign(sty->fields[i], is_root) + " ";
      }

      std::hash<std::string> str_hash;
      temp_name += std::to_string(str_hash(temp));

      sty->set_name(temp_name);
    }

    break;
  }
  default: {
    break;
  }
  }

  return 0;
}

// yuhao: add the struct type to the struct_types
uint64_t SpecificationManager::post_process(Type *ty) {

  if (ty == nullptr) {
    return 0;
  }

  switch (ty->llvmTypeID) {
  case llvm::Type::IntegerTyID: {
    break;
  }
  case llvm::Type::PointerTyID: {
    post_process(((PointerType *)ty)->element_type);
    break;
  }
  case llvm::Type::ArrayTyID: {
    post_process(((ArrayType *)ty)->element_type);
    break;
  }
  case llvm::Type::StructTyID: {

    auto sty = (StructType *)ty;

    if (struct_types.find(sty->get_id()) != struct_types.end()) {
      merge_type(struct_types[sty->get_id()], sty);
    } else {
      struct_types[sty->get_id()] = (StructType *)sty;
    }

    for (auto field : sty->fields) {
      post_process(field);
    }
    break;
  }
  default: {
    break;
  }
  }

  return 0;
}

std::string SpecificationManager::to_sign(Type *ty, bool is_root) {
  // uint64_t debug = 1;
  std::string ret;
  switch (ty->llvmTypeID) {
  case llvm::Type::IntegerTyID: {
    auto ity = ((IntegerType *)ty);
    ret += "int" + std::to_string(ity->bit_width);
    break;
  }
  case llvm::Type::PointerTyID: {
    auto pty = ((PointerType *)ty);
    ret += "ptr[";
    if (pty->element_type == nullptr) {
      // yuhao: the element type is not set, so it is int8
      ret += "array[int8]";
    } else {
      ret += to_sign(pty->element_type, is_root);
    }
    ret += "]";
    break;
  }
  case llvm::Type::ArrayTyID: {
    auto aty = ((ArrayType *)ty);
    ret += "array[";

    if (aty->element_type == nullptr) {
      ret += "int8";
    } else {
      ret += to_sign(aty->element_type);
    }

    if (is_root) {

    } else {
      // for length
      if (aty->length.mode == 1) {
        ret += ", ";
        ret += to_syzlang(&aty->length);
      } else if (aty->length.mode == 2) {
        ret += ", ";
        ret += to_syzlang(&aty->length);
      }
    }

    ret += "]";
    break;
  }
  case llvm::Type::StructTyID: {
    auto sty = ((StructType *)ty);
    ret += sty->get_name();
    break;
  }
  default: {
    hy_log(3, "SpecificationManager::to_sign(): " +
                  std::to_string(ty->llvmTypeID));
    break;
  }
  }
  return ret;
}

std::string SpecificationManager::to_syzlang() {
  std::string ret;

  ret += "meta arches[\"amd64\"]";
  ret += "\n\n";

  for (auto spec : specs) {
    ret += to_syzlang(spec.second) + "\n";
  }

  ret += "\n";
  for (auto sty : struct_types) {
    ret += to_syzlang_with_fields(sty.second) + "\n";
  }

  std::string file_name = "syz_spec_" + this->spec_config->output + ".txt";
  std::ofstream syz_of(this->work_dir + "/" + file_name);
  syz_of << ret;
  syz_of.close();

  return ret;
}

std::string SpecificationManager::to_syzlang(Specification *spec) {
  std::string ret;
  ret += this->spec_config->interface_name;
  ret += "$";
  ret += "syz_spec_";
  ret += std::to_string(this->id);
  ret += "_";
  ret += std::to_string(spec->id);
  ret += "(";
  if (!this->spec_config->prefix.empty()) {
    ret += this->spec_config->prefix;
    ret += ", ";
  }

  uint64_t index = 0;
  for (auto arg : spec->args) {
    ret += "arg" + std::to_string(index++) + " ";
    ret += to_syzlang(arg) + ", ";
  }
  ret = ret.substr(0, ret.size() - 2);

  if (!this->spec_config->suffix.empty()) {
    ret += ", ";
    ret += this->spec_config->suffix;
  }

  ret += ")";
  return ret;
}

std::string SpecificationManager::to_syzlang(Type *ty, Direction d,
                                             bool is_root) {
  // uint64_t debug = 1;
  std::string ret;
  switch (ty->llvmTypeID) {
  case llvm::Type::IntegerTyID: {
    auto ity = ((IntegerType *)ty);
    ret += "int" + std::to_string(ity->bit_width);
    if (d == Direction::OUT) {

    } else if (ity->value.mode == -1) {
      // yuhao: the value does not have constraints, so it is const
      // ret = "const[0, " + ret + "]";
    } else if (ity->value.mode == 0) {
      // yuhao: the value does not get value, so nothing to do
    } else if (ity->value.mode == 1) {
      if (is_root) {
        ret = "const[" + to_syzlang(&ity->value, is_root) + "]";
      } else {
        ret = "const[" + to_syzlang(&ity->value) + ", " + ret + "]";
      }
    } else if (ity->value.mode == 4) {
      ret = "len[" + ity->value.name + ", " + ret + "]";
    } else {
      if (is_root) {
        ret = "const[" + to_syzlang(&ity->value, is_root) + "]";
      } else {
        ret += "[" + to_syzlang(&ity->value) + "]";
      }
    }
    break;
  }
  case llvm::Type::PointerTyID: {
    auto pty = ((PointerType *)ty);
    ret += "ptr[";
    if (pty->direction == Direction::DEFAULT) {
      ret += "in";
    } else if (pty->direction == Direction::IN) {
      ret += "in";
    } else if (pty->direction == Direction::OUT) {
      ret += "out";
    } else if (pty->direction == Direction::INOUT) {
      ret += "inout";
    }
    ret += ", ";
    if (pty->element_type == nullptr) {
      // yuhao: the element type is not set, so it is int8
      ret += "array[int8]";
    } else {
      ret += to_syzlang(pty->element_type, pty->direction, false);
    }
    if (pty->is_opt) {
      ret += ", opt";
    }
    ret += "]";
    break;
  }
  case llvm::Type::ArrayTyID: {
    auto aty = ((ArrayType *)ty);
    ret += "array[";

    if (aty->element_type == nullptr) {
      ret += "int8";
    } else {
      ret += to_syzlang(aty->element_type, d, false);
    }

    // for length
    if (aty->length.mode == 1) {
      ret += ", ";
      ret += to_syzlang(&aty->length);
    } else if (aty->length.mode == 2) {
      ret += ", ";
      ret += to_syzlang(&aty->length);
    }

    // yuhao: todo support model 2 in the future
    ret += "]";
    break;
  }
  case llvm::Type::StructTyID: {
    auto sty = ((StructType *)ty);

    ret += sty->get_name();
    ret += "_";
    ret += std::to_string(this->id);
    break;
  }
  default: {
    hy_log(3, "SpecificationManager::to_syzlang(): " +
                  std::to_string(ty->llvmTypeID));
    break;
  }
  }
  return ret;
}

std::string SpecificationManager::to_syzlang_with_fields(StructType *sty) {
  std::string ret;
  uint64_t field_index = 0;
  ret += sty->get_name();
  ret += "_";
  ret += std::to_string(this->id);
  ret += " {\n";
  for (auto field : sty->fields) {
    ret += "    ";
    ret += "field_" + std::to_string(field_index++);
    ret += "    ";

    // yuhao: if the field is a pointer, we need to add opt if it is
    // optional can improve the code
    std::set<llvm::Type *> checked;
    field->is_opt = is_opt_pointer(sty->st, checked, field->type);

    ret += to_syzlang(field, Direction::DEFAULT, false);
    ret += "\n";
  }

  // yuhao: add packed
  ret += "} [packed]\n";
  // if (sty->is_packed) {
  //   ret += "} [packed]\n";
  // } else {
  //   ret += "}\n";
  // }
  return ret;
}

// yuhao: mode
// -1. do not have constraints
// 0. do not get value
// 1. one const value (0x42),
// 2. range (0:100),
// 3. range with interval (1:10, 2) (todo)
std::string SpecificationManager::to_syzlang(Value *val, bool is_root) {
  std::string ret;
  switch (val->mode) {
  case -1: {
    hy_log(3, "Value::to_syzlang(): -1");
    break;
  }
  case 0: {
    hy_log(3, "Value::to_syzlang(): 0");
    break;
  }
  case 1: {
    ret += std::to_string(val->const_value);
    break;
  }
  case 2: {
    if (is_root) {
      ret += std::to_string(val->const_value);
    } else {
      ret += std::to_string(val->min) + ":" + std::to_string(val->max);
    }
    break;
  }
  case 3: {
    ret += std::to_string(val->min) + ":" + std::to_string(val->max) + "," +
           std::to_string(val->interval);
  } break;
  default: {
    hy_log(3, "Value::to_syzlang(): " + std::to_string(val->mode));
    break;
  }
  }
  return ret;
}

bool is_opt_pointer(llvm::StructType *st, std::set<llvm::Type *> &checked,
                    llvm::Type *t) {

  if (st == nullptr) {
    return false;
  }

  if (t == nullptr) {
    return false;
  }

  if (checked.find(t) == checked.end()) {
    checked.insert(t);
  } else {
    return false;
  }
  switch (t->getTypeID()) {
  case llvm::Type::HalfTyID:
  case llvm::Type::BFloatTyID:
  case llvm::Type::FloatTyID:
  case llvm::Type::DoubleTyID:
  case llvm::Type::X86_FP80TyID:
  case llvm::Type::FP128TyID:
  case llvm::Type::PPC_FP128TyID:
  case llvm::Type::VoidTyID:
  case llvm::Type::LabelTyID:
  case llvm::Type::MetadataTyID:
  case llvm::Type::X86_MMXTyID:
  case llvm::Type::X86_AMXTyID:
  case llvm::Type::TokenTyID:
  case llvm::Type::IntegerTyID:
  case llvm::Type::FunctionTyID:
  case llvm::Type::FixedVectorTyID:
  case llvm::Type::ScalableVectorTyID:
    break;
  case llvm::Type::PointerTyID: {
    if (t->getNumContainedTypes()) {
      return is_opt_pointer(st, checked, t->getNonOpaquePointerElementType());
    }
  }
  case llvm::Type::ArrayTyID: {
    return is_opt_pointer(st, checked, t->getArrayElementType());
  }
  case llvm::Type::StructTyID: {
    if (get_real_structure_name(t->getStructName().str()) ==
        get_real_structure_name(st->getStructName().str())) {
      return true;
    }
    for (int64_t i = 0; i < t->getStructNumElements(); i++) {
      if (is_opt_pointer(st, checked, t->getStructElementType(i))) {
        return true;
      }
    }
    break;
  }
  }
  return false;
}

} // namespace hy