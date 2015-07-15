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

struct Foo {
    x: i32,
}

impl Foo {
    #[precond="self.x < 10"]
    #[precond="y < 10"]
    #[postcond="self.x > 10"]
    #[invariant="self.x < 15"]
    fn foo(&mut self, y: i32) {
        self.x += y; 
    }
    #[postcond="return < 15"]
    fn foo_ret(&mut self, y: i32) -> i32 {
        y 
    }
}

#[test]
fn test_impl_1(){
    let mut f = Foo { x: 5 };
    f.foo(6);
}

#[test]
#[should_panic]
fn test_impl_2(){
    let mut f = Foo { x: 10 };
    f.foo(4);
}

#[test]
#[should_panic]
fn test_impl_3(){
    let mut f = Foo { x: 9 };
    f.foo(9);
}

#[test]
fn test_impl_4(){
    let mut f = Foo { x: 0 };
    f.foo_ret(10);
}

#[test]
#[should_panic]
fn test_impl_5(){
    let mut f = Foo { x: 0 };
    f.foo_ret(16);
}
