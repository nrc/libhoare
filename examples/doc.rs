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

// Examples from readme.md

#[precond="x > 0"]
#[postcond="return > 1"]
fn foo(x: i64) -> i64 {
    let y = 45 / x;
    y + 1
}


struct Bar {
    f1: i64,
    f2: i64
}

#[invariant="x.f1 < x.f2"]
fn baz(x: &mut Bar) {
    x.f1 += 10;
    x.f2 += 10;
}

fn main() {
    foo(12);
    foo(26);
    // task '<main>' failed at 'precondition of foo (x > 0)'
    // foo(-3);

    let mut b = Bar { f1: 0, f2: 10 };
    baz(&mut b);
    b.f2 = 100;
    baz(&mut b);
    b.f2 = -5;
    // task '<main>' failed at 'invariant entering baz (x.f1 < x.f2)'
    // baz(&mut b);
}
