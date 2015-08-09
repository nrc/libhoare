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

#[test]
#[precond="true"]
fn test_trivial_1() {}

#[test]
#[postcond="true"]
fn test_trivial_2() {}

#[test]
#[invariant="true"]
fn test_trivial_3() {}

#[test]
#[precond="true"]
#[postcond="true"]
#[invariant="true"]
fn test_trivial_4() {}

#[test]
#[should_panic]
#[precond="false"]
fn test_fail_trivial_1() {}

#[test]
#[should_panic]
#[postcond="false"]
fn test_fail_trivial_2() {}

#[test]
#[should_panic]
#[invariant="false"]
fn test_fail_trivial_3() {}

#[test]
#[precond="true"]
pub fn pub_test_trivial_1() {}

#[test]
#[postcond="true"]
pub fn pub_test_trivial_2() {}

#[test]
#[invariant="true"]
pub fn pub_test_trivial_3() {}

#[test]
#[precond="true"]
#[postcond="true"]
#[invariant="true"]
pub fn pub_test_trivial_4() {}

#[test]
#[should_panic]
#[precond="false"]
pub fn pub_test_fail_trivial_1() {}

#[test]
#[should_panic]
#[postcond="false"]
pub fn pub_test_fail_trivial_2() {}

#[test]
#[should_panic]
#[invariant="false"]
pub fn pub_test_fail_trivial_3() {}

#[test]
#[precond="4u32 < 5"]
fn test_simple_1() {}

#[test]
#[postcond="'a' == 'a'"]
fn test_simple_2() {}

#[test]
#[invariant="1 >= -1i64"]
fn test_simple_3() {}

#[test]
#[precond="3u8 == 3"]
#[postcond="2i32 > 0"]
#[invariant="0i16 < 500"]
fn test_simple_4() {}

#[test]
#[should_panic]
#[precond="1i8 < 0"]
fn test_fail_simple_1() {}

#[test]
#[should_panic]
#[postcond="'a' == 'b'"]
fn test_fail_simple_2() {}

#[test]
#[should_panic]
#[invariant="true && false"]
fn test_fail_simple_3() {}

#[precond="x < 0"]
fn foo_ta1(x: i32) {}

#[test]
fn test_arg_1() { foo_ta1(-1) }

#[test]
#[should_panic]
fn test_arg_fail_1() { foo_ta1(0) }

#[invariant="x < 0"]
fn foo_ta2(x: i32) {}

#[test]
fn test_arg_2() { foo_ta2(-1) }

#[test]
#[should_panic]
fn test_arg_fail_2() { foo_ta2(0) }

#[postcond="x < 0"]
fn foo_ta3(x: i32) {}

#[test]
fn test_arg_3() { foo_ta3(-1) }

#[test]
#[should_panic]
fn test_arg_fail_3() { foo_ta3(0) }

#[precond="x == \"foo\""]
fn foo_ta4(x: &str) {}

#[test]
fn test_arg_4() { foo_ta4("foo") }

#[test]
#[should_panic]
fn test_arg_fail_4() { foo_ta4("bar") }

#[invariant="x == \"foo\""]
fn foo_ta5(x: &str) {}

#[test]
fn test_arg_5() { foo_ta5("foo") }

#[test]
#[should_panic]
fn test_arg_fail_5() { foo_ta5("bar") }

#[postcond="x == \"foo\""]
fn foo_ta6(x: &str) {}

#[test]
fn test_arg_6() { foo_ta6("foo") }

#[test]
#[should_panic]
fn test_arg_fail_6() { foo_ta6("bar") }

#[postcond="return"]
fn trt() -> bool { true }

#[test]
fn test_result_trivial() { trt(); }

#[postcond="return"]
fn trtf() -> bool { false }

#[test]
#[should_panic]
fn test_result_trivial_fail() { trtf(); }

#[postcond="return > 0"]
fn tr1(x: i32) -> i32 { x }

#[test]
fn test_result_1() { tr1(5); }

#[test]
#[should_panic]
fn test_result_1_fail() { tr1(-5); }

#[postcond="return == 'a'"]
fn tr2(x: char) -> char { x }

#[test]
fn test_result_2() { tr2('a'); }

#[test]
#[should_panic]
fn test_result_2_fail() { tr2('b'); }

#[postcond="return > 5"]
fn tr3(path: bool) -> i32 {
    if path {
        return 42;
    }
    10
}

#[test]
fn test_result3() {
    tr3(true);
    tr3(false);
}

#[postcond="return < 15"]
fn tr3f(path: bool) -> i32 {
    if path {
        return 42;
    }
    10
}

#[test]
#[should_panic]
fn test_result3_fail() {
    tr3f(true);
}

#[precond="*x > 10"]
fn tio1(x: &mut i32) { *x = 25; }

#[test]
fn test_in_out_1() {
    let mut x = 15;
    tio1(&mut x);
}

#[postcond="*x > 10"]
fn tio2(x: &mut i32) { *x = 25; }

#[test]
fn test_in_out_2(){
    let mut x = 15;
    tio2(&mut x);
}

#[invariant="*x > 10"]
fn tio3(x: &mut i32) { *x = 25; }

#[test]
fn test_in_out_3(){
    let mut x = 15;
    tio3(&mut x);
}

#[precond="*x > 10"]
#[postcond="*x > 10"]
#[invariant="*x > 10"]
fn tio4(x: &mut i32) { *x = 25; }

#[test]
fn test_in_out_4(){
    let mut x = 15;
    tio4(&mut x);
}

#[precond="*x > 10"]
fn tio1f(x: &mut i32) { *x = 25; }

#[test]
#[should_panic]
fn test_in_out_1_fail(){
    let mut x = 5;
    tio1f(&mut x);
}

#[postcond="*x > 10"]
fn tio2f(x: &mut i32) { *x = 5; }

#[test]
#[should_panic]
fn test_in_out_2_fail(){
    let mut x = 15;
    tio2f(&mut x);
}

#[invariant="*x > 10"]
fn tio3f(x: &mut i32) { *x = 25; }

#[test]
#[should_panic]
fn test_in_out_3_fail(){
    let mut x = 5;
    tio3f(&mut x);
}

#[invariant="*x > 10"]
fn tio4f(x: &mut i32) { *x = 5; }

#[test]
#[should_panic]
fn test_in_out_4_fail(){
    let mut x = 15;
    tio4f(&mut x);
}
