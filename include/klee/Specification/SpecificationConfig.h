//
// Created by yuhao on 2/12/23.
//

#ifndef KLEE_LINUXKERNEL_H
#define KLEE_LINUXKERNEL_H

#include "klee/Utils/basic.h"
#include "klee/Utils/json.hpp"
#include <cstdint>

namespace klee {
class ExecutionState;
}

namespace hy {

static std::string module_name = "init_module";
const static std::string module_init_name[]{
    "0",  "1", "1s", "2", "2s", "3", "3s", "4",
    "4s", "5", "5s", "6", "6s", "7", "7s", module_name};

class module_init_order {
public:
  uint64_t order;
  std::string name;
  std::set<std::string> function_name;
};

class SpecificationConfig {
public:
  nlohmann::json config;

  std::vector<std::string> entry_functions;

  // yuhao: for Linux kernel
  std::map<std::string, module_init_order *> module_init_function;

  uint64_t arguments_index = 0;
  uint64_t arguments_num = 0;
  std::string interface_name;
  std::string prefix;
  std::string suffix;
  std::string output;

public:
  SpecificationConfig();

  static std::string get_entry_function();

  void read_config();

  void analysis();
};

} // namespace hy

#endif // KLEE_LINUXKERNEL_H
