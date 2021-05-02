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

fn is_release() -> bool {
  std::env::var("OUT_DIR").unwrap().contains("release")
}

fn main() {
  let mut cc = cc::Build::new();
  cc.compiler("clang++")
    .cpp(true)
    .file("src/inline_string.cc")
    .file("src/ffi.cc")
    .flag("-std=c++17");

  if is_release() {
    cc.define("NDEBUG", None)
      .flag("-fembed-bitcode")
      .flag("-O3");
  }

  cc.compile("interop-example-cc");
}
