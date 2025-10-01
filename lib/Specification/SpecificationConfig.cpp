//
// Created by yuhao on 2/12/23.
//

#include "klee/Specification/SpecificationConfig.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Utils/def.h"
#include "klee/Utils/log.h"

#include <fstream>
#include <llvm/Support/CommandLine.h>

llvm::cl::opt<std::string> SpecConfig("spec-config",
                               llvm::cl::desc("The configuration json file."),
                               llvm::cl::init("./config.json"));

llvm::cl::opt<int> SpecArgIndex("spec-arguments-index",
                             llvm::cl::desc("The index of the arguments."),
                             llvm::cl::init(1));

llvm::cl::opt<int> SpecArgNum("spec-arguments-num",
                           llvm::cl::desc("The number of the arguments."),
                           llvm::cl::init(0));

llvm::cl::opt<std::string> SpecInterfaceName("spec-interface-name",
                                          llvm::cl::desc("The interface name."),
                                          llvm::cl::init("ioctl"));

llvm::cl::opt<std::string>
    SpecPrefix("spec-prefix", llvm::cl::desc("The prefix of generated syzlang."),
           llvm::cl::init("fd fd"));

llvm::cl::opt<std::string>
    SpecSuffix("spec-suffix", llvm::cl::desc("The suffix of generated syzlang."),
           llvm::cl::init(""));

llvm::cl::opt<std::string> SpecOutput("spec-output",
                                  llvm::cl::desc("The output file name."),
                                  llvm::cl::init(""));

namespace hy {

SpecificationConfig::SpecificationConfig() {

  uint64_t order = 0;
  for (const auto &temp : module_init_name) {
    auto temp_1 = new module_init_order();
    temp_1->order = order++;
    temp_1->name = "module_init_function_" + temp;
    module_init_function[temp] = temp_1;
  }

  arguments_index = SpecArgIndex;
  arguments_num = SpecArgNum;
  interface_name = SpecInterfaceName.c_str();
  prefix = SpecPrefix.c_str();
  suffix = SpecSuffix.c_str();
  output = SpecOutput.c_str();

  hy_log(1, "arguments_index: " + std::to_string(arguments_index));
  hy_log(1, "arguments_num: " + std::to_string(arguments_num));
  hy_log(1, "interface_name: " + interface_name);
  hy_log(1, "prefix: " + prefix);
  hy_log(1, "suffix: " + suffix);
  hy_log(1, "output: " + output);

}

std::string SpecificationConfig::get_entry_function() {
  std::ifstream json_in_file_stream(SpecConfig);
  nlohmann::json config;
  if (json_in_file_stream.is_open()) {
    json_in_file_stream >> config;
  } else {
    hy_log(3, "open config json file fail: " + SpecConfig);
    return "";
  }

  std::string key;
  key = ENTRYPOINT;
  std::string ret;
  if (config.contains(key) && config[key].is_string()) {
    ret = config[key].get<std::string>();
  }
  return ret;
}

void SpecificationConfig::read_config() {
  std::ifstream json_in_file_stream(SpecConfig);
  if (json_in_file_stream.is_open()) {
    json_in_file_stream >> this->config;
  } else {
    hy_log(3, "open config json file fail: " + SpecConfig);
    return;
  }

  std::string key;
  key = MODULES;
  if (config.contains(key) && config[key].is_object()) {
    for (const auto &it : config[key].items()) {
      if (module_init_function.find(it.key()) == module_init_function.end()) {
        hy_log(3, "not find " + it.key() + " in module_init_function");
        continue;
      }
      if (!it.value().is_array()) {
        hy_log(3, it.key() + " is not array");
        continue;
      }
      auto temp_1 = module_init_function[it.key()];
      for (const auto &itt : it.value()) {
        temp_1->function_name.insert(itt.get<std::string>());
      }
    }

    for (const auto &it : module_init_function) {
      for (const auto &itt : it.second->function_name) {
        entry_functions.push_back(itt);
      }
    }
  }
}

void SpecificationConfig::analysis() {}
} // namespace hy
