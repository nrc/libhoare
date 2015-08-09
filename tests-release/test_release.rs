// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(plugin, custom_attribute)]
#![plugin(hoare)]

// The code below should execute with no output in "--release" mode
// and panick otherwise.

#[debug_precond="false"]
fn test_precondition_ignored_for_release() {}

fn main() {
    test_precondition_ignored_for_release();
}
