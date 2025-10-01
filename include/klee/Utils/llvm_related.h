//
// Created by yu on 5/2/21.
//

#ifndef INC_LLVM_RELATED_H
#define INC_LLVM_RELATED_H

#include "basic.h"
#include "log.h"

#define hy_llvm_print(type, empty, out, print, str)                            \
  if ((type) >= LOG_LEVEL) {                                                   \
    if ((empty) == 1) {                                                        \
      (str) = "";                                                              \
    }                                                                          \
    llvm::raw_string_ostream dump(str);                                        \
    print(dump);                                                               \
    if ((out) == 1) {                                                          \
      hy_log(type, str);                                                       \
    }                                                                          \
  }

#define hy_add(type, print, str) hy_llvm_print(type, 0, 0, print, str)
#define hy_print(type, print, str) hy_llvm_print(type, 1, 0, print, str)
#define hy_dump(type, print, str) hy_llvm_print(type, 1, 1, print, str)
#define hy_add_dump(type, print, str) hy_llvm_print(type, 0, 1, print, str)

// for optimized bitcode
static llvm::BasicBlock *get_real_basic_block(llvm::BasicBlock *b) __attribute__ ((unused));

static llvm::BasicBlock *get_final_basic_block(llvm::BasicBlock *b) __attribute__ ((unused));

// for linked bitcode
static std::string get_real_function_name(llvm::Function *f) __attribute__ ((unused));

static std::string get_real_structure_name(const std::string &name) __attribute__ ((unused));

static llvm::Type *get_real_type(llvm::Type *t) __attribute__ ((unused));

static std::string get_real_function_type(llvm::FunctionType *ft) __attribute__ ((unused));

// for debug info
static std::string get_file_name(llvm::Function *f) __attribute__ ((unused));

static std::string dump_inst(llvm::Instruction *inst) __attribute__ ((unused));

static std::string dump_inst_bootlin(llvm::Instruction *inst,
                                     const std::string &version = "latest") __attribute__ ((unused));

static std::string dump_function_bootlin(llvm::Function *func,
                                         const std::string &version = "latest") __attribute__ ((unused));

static uint64_t get_loc(llvm::Function *func) __attribute__ ((unused));

// for inst str
static std::string real_inst_str(std::string str) __attribute__ ((unused));

// strID: Path-NameFunction-NoBB-NoInst
static std::string function_to_strID(llvm::Function *f) __attribute__ ((unused));

static std::string bb_to_strID(llvm::BasicBlock *b) __attribute__ ((unused));

static std::string inst_to_strID(llvm::Instruction *inst) __attribute__ ((unused));

static llvm::Function *strID_to_function(llvm::Module *m,
                                         const std::string &str) __attribute__ ((unused));

static llvm::BasicBlock *strID_to_bb(llvm::Module *m, const std::string &str) __attribute__ ((unused));

static llvm::Instruction *strID_to_inst(llvm::Module *m,
                                        const std::string &str) __attribute__ ((unused));

/// Compute the true target of a function call, resolving LLVM aliases
/// and bit casts.
static llvm::Function *get_target_function(llvm::Value *calledVal) __attribute__ ((unused));

llvm::BasicBlock *get_real_basic_block(llvm::BasicBlock *b) {
  llvm::BasicBlock *real_basic_block = b;
  while (!real_basic_block->hasName()) {
    for (auto *pred : llvm::predecessors(real_basic_block)) {
      real_basic_block = pred;
      break;
    }
  }
  return real_basic_block;
}

llvm::BasicBlock *get_final_basic_block(llvm::BasicBlock *b) {
  auto *inst = b->getTerminator();
  for (unsigned int i = 0, end = inst->getNumSuccessors(); i < end; i++) {
    if (inst->getSuccessor(i)->hasName()) {
    } else {
      return get_final_basic_block(inst->getSuccessor(i));
    }
  }
  return b;
}

std::string get_real_function_name(llvm::Function *f) {
  std::string name = f->getName().str();
  std::string ret;
  if (name.find('.') != std::string::npos) {
    ret = name.substr(0, name.find('.'));
  } else {
    ret = name;
  }
  return ret;
}

std::string get_real_structure_name(const std::string &name) {
  std::string ret;
  uint64_t index_1 = name.find('.');
  if (index_1 != std::string::npos) {
    uint64_t index_2 = name.find('.', index_1 + 1);
    if (index_2 != std::string::npos) {
      ret = name.substr(0, index_2);
    } else {
      ret = name;
    }
  } else {
    ret = name;
    hy_log(3, "get_structure_name: " + name);
  }
  return ret;
}

llvm::Type *get_real_type(llvm::Type *t) {
  if (t == nullptr) {
    return nullptr;
  }
  if (t->isPointerTy()) {
    return get_real_type(t->getNonOpaquePointerElementType());
  } else if (t->isArrayTy()) {
    return get_real_type(t->getArrayElementType());
  } else if (t->isVectorTy()) {
    return get_real_type(t->getScalarType());
  }
  return t;
}

std::string get_real_function_type(llvm::FunctionType *ft) {
  std::string type;
  std::string str;
  int64_t debug = 4;
  auto ret = ft->getReturnType();
  if (ret->isPointerTy() &&
      ret->getNonOpaquePointerElementType()->isStructTy()) {
    hy_print(debug, ret->print, str) str = str.substr(0, str.size() - 1);
    if (str.find("struct") == std::string::npos) {
      type += str;
    } else {
      type += (get_real_structure_name(str) + "*");
    }
  } else if (ret->isStructTy()) {
    hy_print(debug, ret->print,
             str) if (str.find("struct") == std::string::npos) {
      type += str;
    }
    else {
      type += get_real_structure_name(str);
    }
  } else {
    hy_print(debug, ret->print, str) type += str;
  }
  type += " (";
  for (uint64_t i = 0; i < ft->getNumParams(); i++) {
    if (i != 0) {
      type += ", ";
    }
    auto temp = ft->getParamType(i);
    if (temp->isPointerTy() &&
        temp->getNonOpaquePointerElementType()->isStructTy()) {
      hy_print(debug, temp->print, str) str = str.substr(0, str.size() - 1);
      if (str.find("struct") == std::string::npos) {
        type += str;
      } else {
        type += (get_real_structure_name(str) + "*");
      }
    } else if (temp->isStructTy()) {
      hy_print(debug, temp->print,
               str) if (str.find("struct") == std::string::npos) {
        type += str;
      }
      else {
        type += get_real_structure_name(str);
      }
    } else {
      hy_print(debug, temp->print, str) type += str;
    }
  }
  type += ")";
  return type;
}

std::string get_file_name(llvm::Function *f) {
  if (f->hasMetadata()) {
    llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 4> MDs;
    f->getAllMetadata(MDs);
    for (auto &MD : MDs) {
      llvm::MDNode *N = MD.second;
      if (N == nullptr) {
        continue;
      }
      auto *SP = llvm::dyn_cast<llvm::DISubprogram>(N);
      if (SP == nullptr) {
        continue;
      }
      std::string path = SP->getFilename().str();
      return path;
    }
  }
  return "";
}

std::string dump_inst(llvm::Instruction *inst) {
  std::string ret;
  if (inst == nullptr) {
    return ret;
  }

  auto b = inst->getParent();
  auto f = b->getParent();
  if (inst->hasMetadata()) {
    const llvm::DebugLoc &debug_info = inst->getDebugLoc();
    if (debug_info) {
      std::string path = debug_info->getFilename().str();
      ret += "path: " + path;
      unsigned int line = debug_info->getLine();
      unsigned int column = debug_info->getColumn();
      ret += "; line: " + std::to_string(line);
      ret += "; column: " + std::to_string(column);
    }
    llvm::DILocation *inline_at = debug_info->getInlinedAt();
    while (inline_at != nullptr) {
      ret += "\n\t\tinline at: ";
      std::string path = inline_at->getFilename().str();
      ret += "path: " + path;
      unsigned int line = inline_at->getLine();
      unsigned int column = inline_at->getColumn();
      ret += "; line: " + std::to_string(line);
      ret += "; column: " + std::to_string(column);
      inline_at = inline_at->getInlinedAt();
    }
    ret += "; function: " + get_real_function_name(f);
  } else {
    std::string path = get_file_name(f);
    ret += "path: " + path;
    ret += "; function: " + get_real_function_name(f);
  }
  return ret;
}

std::string dump_inst_bootlin(llvm::Instruction *inst,
                              const std::string &version) {
  std::string ret;

  if (inst != nullptr) {
    //            inst->dump();
  } else {
    return ret;
  }
  auto b = inst->getParent();
  auto f = b->getParent();

  unsigned int line = 1;
  std::string path = get_file_name(f);
  if (inst->hasMetadata()) {
    const llvm::DebugLoc &debug_info = inst->getDebugLoc();
    if (debug_info) {
      path = debug_info->getFilename().str();
      line = debug_info->getLine();
    }
  }

  ret += "https://elixir.bootlin.com/linux/";
  ret += version;
  ret += "/source/";
  ret += path + "#L" + std::to_string(line);
  return ret;
}

std::string dump_function_bootlin(llvm::Function *func,
                                  const std::string &version) {
  std::string ret;

  if (func != nullptr) {
    //            inst->dump();
  } else {
    return ret;
  }

  unsigned int line = 1;
  std::string path;

  if (func->hasMetadata()) {
    llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 4> MDs;
    func->getAllMetadata(MDs);
    for (auto &MD : MDs) {
      llvm::MDNode *N = MD.second;
      if (N == nullptr) {
        continue;
      }
      auto *sp = llvm::dyn_cast<llvm::DISubprogram>(N);
      if (sp == nullptr) {
        continue;
      }
      line = sp->getLine();
      path = sp->getFilename().str();
      break;
    }
  }

  ret += "https://elixir.bootlin.com/linux/";
  ret += version;
  ret += "/source/";
  ret += path + "#L" + std::to_string(line);
  return ret;
}

std::string real_inst_str(std::string str) {
  auto index = str.find_last_of('#');
  if (index == std::string::npos) {
    return str;
  } else {
    return str.substr(0, index);
  }
}

uint64_t get_loc(llvm::Function *func) {
  uint64_t line = 0;
  uint64_t start = 0, end = 0;
  std::string file;

  if (func == nullptr) {
    return line;
  }

  if (func->hasMetadata()) {
    llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 4> MDs;
    func->getAllMetadata(MDs);
    for (auto &MD : MDs) {
      llvm::MDNode *N = MD.second;
      if (N == nullptr) {
        continue;
      }
      auto *sp = llvm::dyn_cast<llvm::DISubprogram>(N);
      if (sp == nullptr) {
        continue;
      }
      start = sp->getLine();
      file = sp->getFilename().str();
      break;
    }
  }

  for (auto &bb : *func) {
    for (auto &inst : bb) {
      if (inst.hasMetadata()) {
        const llvm::DebugLoc &debug_info = inst.getDebugLoc();
        if (debug_info) {
          auto temp_file = debug_info->getFilename().str();
          if (file == temp_file) {
            auto temp_line = debug_info->getLine();
            end = temp_line > end ? temp_line : end;
          }
        }
      }
    }
  }
  line = end - start;
  return line > 0 ? line : 0;
}

/// Compute the true target of a function call, resolving LLVM aliases
/// and bit casts.
llvm::Function *get_target_function(llvm::Value *calledVal) {
  llvm::SmallPtrSet<const llvm::GlobalValue *, 3> Visited;

  auto *c = llvm::dyn_cast<llvm::Constant>(calledVal);
  if (!c)
    return nullptr;

  while (true) {
    if (auto *gv = llvm::dyn_cast<llvm::GlobalValue>(c)) {
      if (!Visited.insert(gv).second)
        return nullptr;

      if (auto *f = llvm::dyn_cast<llvm::Function>(gv))
        return f;
      else if (auto *ga = llvm::dyn_cast<llvm::GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return nullptr;
    } else if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode() == llvm::Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return nullptr;
    } else
      return nullptr;
  }
}

std::string function_to_strID(llvm::Function *f) {
  std::string ret;
  if (f == nullptr) {
    return ret;
  }
  std::string Path = get_file_name(f);
  std::string NameFunction = f->getName().str();
  ret += Path;
  ret += DELIMITER;
  ret += NameFunction;
  return ret;
}

std::string bb_to_strID(llvm::BasicBlock *b) {
  std::string ret;
  if (b == nullptr) {
    return ret;
  }
  auto f = b->getParent();
  ret += function_to_strID(f);
  int64_t No;
  No = 0;
  for (auto &bb : *f) {
    if (b == &bb) {
      break;
    }
    No++;
  }
  int64_t NoBB = No;
  ret += DELIMITER;
  ret += std::to_string(NoBB);
  return ret;
}

std::string inst_to_strID(llvm::Instruction *inst) {
  std::string ret;
  if (inst == nullptr) {
    return ret;
  }
  auto b = inst->getParent();
  ret += bb_to_strID(b);
  int64_t No;
  No = 0;
  for (auto &i : *b) {
    if (inst == &i) {
      break;
    }
    No++;
  }
  int64_t NoInst = No;
  ret += DELIMITER;
  ret += std::to_string(NoInst);
  return ret;
}

llvm::Function *strID_to_function(llvm::Module *m, const std::string &str) {
  uint64_t start;
  start = str.find(DELIMITER);
  if (start == str.size()) {
    hy_log(3, "no function: " + str);
    return nullptr;
  }
  uint64_t end = str.find(DELIMITER, start + 1);
  std::string NameFunction = str.substr(start + 1, end - start - 1);
  llvm::Function *f = m->getFunction(NameFunction);
  if (f == nullptr) {
    hy_log(3, "bad function name str: " + str);
    hy_log(3, "bad function name: " + NameFunction);
  }
  return f;
}

llvm::BasicBlock *strID_to_bb(llvm::Module *m, const std::string &str) {
  llvm::Function *f = strID_to_function(m, str);
  if (f == nullptr) {
    return nullptr;
  }
  uint64_t start;
  start = str.find(DELIMITER);
  start = str.find(DELIMITER, start + 1);
  if (start == str.size()) {
    hy_log(3, "no basic block: " + str);
    return nullptr;
  }
  uint64_t end = str.find(DELIMITER, start + 1);
  std::string NoBB = str.substr(start + 1, end - start - 1);
  int64_t No = std::stoi(NoBB);
  llvm::BasicBlock *b = nullptr;
  for (auto &bb : *f) {
    if (No == 0) {
      b = &bb;
      break;
    }
    No--;
  }
  return b;
}

llvm::Instruction *strID_to_inst(llvm::Module *m, const std::string &str) {
  llvm::BasicBlock *b = strID_to_bb(m, str);
  if (b == nullptr) {
    return nullptr;
  }
  uint64_t start;
  start = str.find(DELIMITER);
  start = str.find(DELIMITER, start + 1);
  start = str.find(DELIMITER, start + 1);
  if (start == str.size()) {
    hy_log(3, "no inst: " + str);
    return nullptr;
  }
  uint64_t end = str.find(DELIMITER, start + 1);
  std::string NoInst = str.substr(start + 1, end - start - 1);
  int64_t No = std::stoi(NoInst);
  llvm::Instruction *i;
  for (auto &ii : *b) {
    if (No == 0) {
      i = &ii;
      break;
    }
    No--;
  }
  return i;
}

#endif // INC_LLVM_RELATED_H
