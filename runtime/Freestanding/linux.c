//
// Created by yuhao on 2/21/23.
//
#include "stdbool.h"
#include "stdlib.h"
#include "string.h"

unsigned long _find_first_zero_bit(const unsigned long *addr,
                                   unsigned long size) {
  unsigned long pos = 0;
  bool *bool_addr = (bool *)addr;
  // Check each bit of the number from the right to the left
  while ((*(bool_addr + pos) & 1) && pos < size) {
    pos++;
  }
  return pos;
}

unsigned long _find_next_zero_bit(const unsigned long *addr, unsigned long size,
                                  unsigned long pos) {
  bool *bool_addr = (bool *)addr;
  // Check each bit of the number from the right to the left
  while ((*(bool_addr + pos) & 1) && pos < size) {
    pos++;
  }
  return pos;
}

// yuhao: copy_from_user and copy_to_user
unsigned long _copy_from_user(void *to, const void *from, unsigned long n) {
  memcpy(to, from, n);
  return 0;
}

unsigned long _copy_to_user(void *to, const void *from, unsigned long n) {
  memcpy(to, from, n);
  return 0;
}

void *kmemdup(void *from, unsigned long size, unsigned flag) {
  void *new = malloc(size);
  _copy_from_user(new, from, size);
  return new;
}

void *memdup_user(const void *from, unsigned long size) {
  void *new = malloc(size);
  _copy_from_user(new, from, size);
  return new;
}

void *memdup_user_nul(const void *from, unsigned long size) {
  void *new = malloc(size + 1);
  _copy_from_user(new, from, size);
  return new;
}