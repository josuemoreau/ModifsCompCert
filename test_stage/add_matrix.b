void add_matrix(i64[m, n] a, i64[m, n] b, mut i64[m, n] dest, u64 m, u64 n) {
  for u64 i <- 0 .. m {
    for u64 j <- 0 .. n {
      dest[i, j] <- a[i, j] + b[i, j]
    }
  }
}