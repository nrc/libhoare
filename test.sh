cargo test
echo cfail tests
echo
$RUSTC tests-cfail/cfail-1.rs -L ./target
$RUSTC tests-cfail/cfail-2.rs -L ./target
$RUSTC tests-cfail/cfail-3.rs -L ./target
$RUSTC tests-cfail/cfail-4.rs -L ./target
$RUSTC tests-cfail/cfail-5.rs -L ./target
$RUSTC tests-cfail/cfail-6.rs -L ./target
echo