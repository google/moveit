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

pub mod ffi;
use ffi::InlineString;

use moveit::ctor;
use moveit::emplace;
use moveit::Emplace as _;

fn main() {
  let s = Box::emplace(InlineString::from_bytes(b"Hello!"));
  println!("{:p} = {:?}", s.c_str(), s.c_str());

  emplace!(let mut s2 = ctor::copy(&*s));
  println!("{:p} = {:?}", s2.c_str(), s2.c_str());
  for i in 0u8..40 {
    s2.as_mut().push_back(b'a' + i);
    println!("{:p} = {:?}", s2.c_str(), s2.c_str());
  }
  println!("{:p} = {:?}", s.c_str(), s.c_str());

  emplace!(let mut s3 = ctor::mov(s));
  while !s3.empty() {
    println!("{}", s3.as_mut().pop_back());
  }
}
