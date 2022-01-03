// Copyright 2022 Google LLC
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

// Build in test mode only to test cxx integration.

#ifndef CXX_SUPPORT_TEST_CPP
#define CXX_SUPPORT_TEST_CPP

#include <cstdint>
#include <cstring>
#include <memory>

constexpr uint8_t kUninitialized = 0;
constexpr uint8_t kInitialized = 1;
constexpr uint8_t kMethodCalled = 2;

class Foo {
 public:
  Foo() { data[0] = kInitialized; }
  uint8_t get_status() const { return data[0]; }
  void modify() { data[0] = kMethodCalled; }

 private:
  uint32_t data[4];  // exactly match layout declared in Rust.
};

inline Foo* CreateUninitializedFoo() {
  std::allocator<Foo> alloc;
  Foo* data = alloc.allocate(1);
  std::memcpy(data, &kUninitialized, 1);
  return data;
}

inline void FreeUninitializedFoo(Foo* foo) {
  std::allocator<Foo> alloc;
  alloc.deallocate(foo, 1);
}

inline void foo_constructor(Foo& foo) { new (&foo) Foo(); }

#endif  // CXX_SUPPORT_TEST_CPP