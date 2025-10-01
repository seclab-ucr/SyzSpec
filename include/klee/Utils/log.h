//
// Created by yuhao on 5/2/21.
//

#ifndef INC_2021_TEMPLATE_LOG_H
#define INC_2021_TEMPLATE_LOG_H

#include "basic.h"

static const std::string log_file = "log.txt";

static void hy_start_log() __attribute__ ((unused));

static std::string get_time() {
  time_t current_time;
  current_time = time(nullptr);
  std::string time = ctime(&current_time);
  time = time.substr(0, time.size() - 1);
  return time;
}

static std::string print_stack_trace() {
  std::string str;
  llvm::raw_string_ostream dump(str);
  llvm::sys::PrintStackTrace(dump);
  return str;
}

// number: 0(debug), 1(info), 2(warning), 3(error)
static void hy_log(int64_t type, const std::string &message) {
  if (type < LOG_LEVEL) {
    return;
  }
  std::string log_message;

#if LOG_FILE
  auto *err_buf = std::cerr.rdbuf();
  std::ofstream log_ofstream(log_file, std::ios_base::app);
  std::cerr.rdbuf(log_ofstream.rdbuf());
#endif
#if LOG_TIME
  log_message += get_time() + ": ";
#endif

  log_message += message;

  switch (type) {
  case -1: {
    std::cerr << "Low: ";
    std::cerr << log_message;
    break;
  }
  case 0: {
    std::cerr << "Debug: ";
    std::cerr << log_message;
    break;
  }
  case 1: {
#if LOG_COLOR
    std::cerr << LOG_GRN;
#endif
    std::cerr << "Info: ";
    std::cerr << log_message;
#if LOG_COLOR
    std::cerr << LOG_NRM;
#endif
    break;
  }
  case 2: {
#if LOG_COLOR
    std::cerr << LOG_YEL;
#endif
    std::cerr << "Warning: ";
    std::cerr << log_message;
#if LOG_COLOR
    std::cerr << LOG_NRM;
#endif
    break;
  }
  case 3: {
#if LOG_COLOR
    std::cerr << LOG_RED;
#endif
    std::cerr << "Error: ";
    std::cerr << log_message << std::endl;
    std::cerr << print_stack_trace() << std::endl;
#if LOG_COLOR
    std::cerr << LOG_NRM;
#endif
    break;
  }
  default: {
    std::cerr << log_message;
  }
  }
  std::cerr << std::endl;
#if LOG_FILE
  std::cerr.rdbuf(err_buf);
  log_ofstream.close();
#endif
}

static void hy_start_log() {
  std::string log_message;

#if LOG_FILE
  auto *err_buf = std::cerr.rdbuf();
  std::ofstream log_ofstream(log_file);
  std::cerr.rdbuf(log_ofstream.rdbuf());
#endif
#if LOG_TIME
  log_message += get_time() + ": ";
#endif

  log_message += "Start log\n";
  std::cerr << log_message;

#if LOG_FILE
  std::cerr.rdbuf(err_buf);
  log_ofstream.close();
#endif
}

#endif // INC_2021_TEMPLATE_LOG_H
