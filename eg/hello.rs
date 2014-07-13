// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(phase)]

#[phase(plugin)]
extern crate hoare;

#[precond="x != 0"]
fn foo(x: int) {
    println!("hello world! {}", x);    
}

#[debug_invariant="*x > 60"]
fn bar<X: std::fmt::Show>(x: &mut int, y: X) -> int {
    println!("hello world! {} {}", x, y);
    *x += 20;
    35
}

fn main() {
    // A very simple example.
    foo(1);

    // A slightly more interesting test case.
    let mut x = 65;
    bar::<int>(&mut x, 10);
}
