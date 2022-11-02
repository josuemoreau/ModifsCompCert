i64 f(i64 a, i64 b) {
    i64 x <- a + 1;
    return x + b
}

void add_vectors(i64[n] a, i64[n] b, mut i64[n] dest, u64 n) {
    for u64 i <- 0 to n - 1 {
        dest[i] <- a[i] + b[i]
    }
}

i32 main() {
    i64 a <- 1;
    i64 b <- 3;
    f(a, b);
    return 0
}