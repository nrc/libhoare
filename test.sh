echo cfail tests
echo
$RUSTC test/cfail-1.rs -L ../obj
$RUSTC test/cfail-2.rs -L ../obj
$RUSTC test/cfail-3.rs -L ../obj
$RUSTC test/cfail-4.rs -L ../obj
$RUSTC test/cfail-5.rs -L ../obj
$RUSTC test/cfail-6.rs -L ../obj
echo
echo unit tests
echo
$RUSTC test/mod.rs --test -L ../obj -o ../obj/test
../obj/test
