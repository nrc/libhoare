#!/bin/sh
cargo test

RUSTC=`which rustc`

echo
echo Test that release version excludes debug
cargo build --release
# Assuming the -C settings below create a release level version?
$RUSTC tests-release/test_release.rs \
    -C opt-level=3 \
    -C debug-assertions=off \
    --out-dir ./target/release \
    -L ./target/release
if ./target/release/test_release
then
    echo "Test result: Success"
else
    echo "Test result: Fail!"
fi

echo
echo Test that compile failures are comprehensible
echo
$RUSTC tests-cfail/cfail-1.rs -L ./target/debug
$RUSTC tests-cfail/cfail-2.rs -L ./target/debug
$RUSTC tests-cfail/cfail-3.rs -L ./target/debug
$RUSTC tests-cfail/cfail-4.rs -L ./target/debug
$RUSTC tests-cfail/cfail-5.rs -L ./target/debug
$RUSTC tests-cfail/cfail-6.rs -L ./target/debug
echo
