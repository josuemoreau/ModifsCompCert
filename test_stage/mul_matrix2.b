extern void print_matrix(i64[m, n] a, u64 m, u64 n)
extern void print_line()

void mul_matrix(i64[m, n] a, i64[n, p] b, mut i64[m, p] dest, u64 m, u64 n, u64 p) {
  for u64 i <- 0 .. m
    for u64 j <- 0 .. p {
      dest[i, j] <- 0;
      for u64 k <- 0 .. n
        dest[i, j] <- dest[i, j] + a[i, k] * b[k, j]
    }
}
