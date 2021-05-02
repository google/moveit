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

#include "inline_string.h"

InlineString::InlineString(const char* data, std::size_t len) {
  auto actual_len = len + 1;  // Account for a nul.
  if (actual_len > sizeof(repr_))  {
    data_ = new char[len];
    repr_.len_ = len;
    repr_.cap_ = len;
  }

  std::memcpy(data_, data, len);
  data_[len] = '\0';
}

  InlineString& InlineString::operator=(const InlineString& that) {
    reserve(that.size());
    std::strcpy(data_, that.data_);
    return *this;
  }

InlineString& InlineString::operator=(InlineString&& that) {
  if (that.IsSso()) {
    std::strcpy(data_, that.data_);
  } else {
    if (!IsSso()) {
      delete[] data_;
    }
    data_ = that.data_;
    repr_ = that.repr_;

    new (&that) InlineString();
  }
  return *this;
}

  void InlineString::reserve(std::size_t new_cap) {
    if (new_cap < capacity()) {
      return;
    }

    // Growing the buffer always switches us over to heap mode.
    //
    // For illustration's sake, we're not going to fuss with realloc().
    repr_.cap_ = std::max(capacity() * 2, new_cap);
    auto* new_buf = new char[repr_.cap_ + 1];
    std::memcpy(new_buf, data_, size() + 1);
    data_ = new_buf;
  }


  void InlineString::clear() {
    if (!IsSso()) {
      repr_.len_ = 0;
    }
    data_[0] = '\0';
  }

  void InlineString::push_back(char c) {
    auto len = size();
    reserve(len + 1);
    data_[len] = c;
    data_[len + 1] = '\0';
    if (!IsSso()) {
      ++repr_.len_;
    }
  }

  char InlineString::pop_back() {
    auto len = size();
    auto c = data_[len - 1];
    data_[len - 1] = '\0';
    if (!IsSso()) {
      --repr_.len_;
    }
    return c;
  }