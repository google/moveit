// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// FFI bindings on the C++ side.
//
// These thunks are technically all unnecessary with intimate knowledge of the
// ABI, and are provided like this mostly to avoid having to think about it.

#include "inline_string.h"

#include <cstdio>
#include <utility>

#ifndef NDEBUG
#define TRACE(name, ...) \
  std::fprintf(stderr, "  FFI call: `" name "`\n", ##__VA_ARGS__)
#else
#define TRACE(...)
#endif

extern "C" {

InlineString* ffi_InlineString_ctor_default(void* buf) {
  TRACE("InlineString()");
  return new (buf) InlineString();
}

InlineString* ffi_InlineString_ctor_c_str(void* buf, const char* c_str) {
  TRACE("InlineString(const char*)");
  return new (buf) InlineString(c_str);
}

InlineString* ffi_InlineString_ctor_bytes(void* buf, const char* data,
                                          std::size_t len) {
  TRACE("InlineString(const char*, size_t)");
  return new (buf) InlineString(data, len);
}

InlineString* ffi_InlineString_ctor_copy(void* buf, const InlineString* that) {
  TRACE("InlineString(const InlineString&)");
  return new (buf) InlineString(*that);
}

InlineString* ffi_InlineString_ctor_move(void* buf, InlineString* that) {
  TRACE("InlineString(InlineString&&)");
  return new (buf) InlineString(std::move(*that));
}

void ffi_InlineString_dtor(InlineString* self) {
  TRACE("~InlineString(%p)", self);
  self->~InlineString();
}

const char* ffi_InlineString_data(const InlineString* self) {
  TRACE("InlineString::data(%p)", self);
  return self->data();
}

const char* ffi_InlineString_c_str(const InlineString* self) {
  TRACE("InlineString::c_str(%p)", self);
  return self->c_str();
}

bool ffi_InlineString_empty(const InlineString* self) {
  TRACE("InlineString::empty(%p)", self);
  return self->empty();
}
std::size_t ffi_InlineString_size(const InlineString* self) {
  TRACE("InlineString::size(%p)", self);
  return self->size();
}
std::size_t ffi_InlineString_length(const InlineString* self) {
  TRACE("InlineString::length(%p)", self);
  return self->length();
}

std::size_t ffi_InlineString_capacity(const InlineString* self) {
  TRACE("InlineString::capacity(%p)", self);
  return self->capacity();
}
void ffi_InlineString_reserve(InlineString* self, std::size_t new_cap) {
  TRACE("InlineString::reserve(%p)", self);
  self->reserve(new_cap);
}

const char* ffi_InlineString_operator_index_const(const InlineString* self,
                                                  std::size_t index) {
  TRACE("InlineString::operator[](%p)", self);
  return &(*self)[index];
}
char* ffi_InlineString_operator_index(InlineString* self, std::size_t index) {
  TRACE("InlineString::operator[](%p)", self);
  return &(*self)[index];
}

void ffi_InlineString_clear(InlineString* self) {
  TRACE("InlineString::clear(%p)", self);
  self->clear();
}
void ffi_InlineString_push_back(InlineString* self, char c) {
  TRACE("InlineString::push_back(%p)", self);
  self->push_back(c);
}
char ffi_InlineString_pop_back(InlineString* self) {
  TRACE("InlineString::pop_back(%p)", self);
  return self->pop_back();
}
}  // extern "C"