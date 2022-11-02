i64 f(i64 a, i64 b) {
    i64 x <- a + 1;
    return x + b
}

i32 main() {
    i64 a <- 1;
    i64 b <- 3;
    f(a, b);
    return 0
}