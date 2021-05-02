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

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>

// A libstdc++-style SSO string, which uses a self-pointer (and is thus not
// trivially relocatable).
// 
// We implement a subset of the C++ std::string API.
class InlineString {
 public:
  // Create an empty string.
  InlineString() {}

  // Create a string from a nul-terminated C string.
  InlineString(const char* c_str) : InlineString(c_str, std::strlen(c_str)) {}

  // Create a string from the given data and length.
  InlineString(const char* data, std::size_t len);

  InlineString(const InlineString& that) : InlineString(that.data(), that.size()) {}
  InlineString& operator=(const InlineString& that);
  InlineString(InlineString&& that) { *this = that; }
  InlineString& operator=(InlineString&& that);

  ~InlineString() {
    if (!IsSso()) {
      delete[] data_;
    }
  }

  const char* data() const { return data_; }
  const char* c_str() const { return data_; }

  bool empty() const {
    return size() == 0;
  }
  std::size_t size() const {
    return IsSso() ? std::strlen(data_) : repr_.len_; 
  }
  std::size_t length() const {
    return size();
  }

  std::size_t capacity() const {
    return IsSso() ? sizeof(repr_) - 1 : repr_.cap_; 
  }
  void reserve(std::size_t new_cap);

  const char& operator[](std::size_t idx) const {
    return data_[idx];
  }
  char& operator[](std::size_t idx) {
    return data_[idx];
  }

  void clear();
  void push_back(char c);
  char pop_back();

 private:
  bool IsSso() const {
    // When the address of `data_` is equal to the address of `repr_`, we're in
    // SSO mode.
    return data_ == reinterpret_cast<const char*>(&repr_);
  }

  char* data_ = reinterpret_cast<char*>(&repr_);
  struct {
    std::size_t len_ = 0;
    std::size_t cap_ = 0;
  } repr_;
};

static_assert(sizeof(InlineString) / sizeof(std::uintptr_t) == 3);
static_assert(alignof(InlineString) == alignof(std::uintptr_t));