$RUSTC eg/hello.rs -L ../obj -o ../obj/hello
$RUSTC eg/hello.rs -L ../obj -o ../obj/doc
$RUSTC eg/hello.rs -L ../obj -o ../obj/lexer

../obj/hello
../obj/doc
../obj/lexer
