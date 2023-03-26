void mul_matrix(i64[n] a, i64[n] b, mut i64[n] dest, u64 n, u64 m) {
  /* on aimerait ici pouvoir dire que a, b et dest sont de taille n * n,
     ou encore m * n et n * p */
  for u64 i <- 0 .. m {
    for u64 j <- 0 .. m {
      dest[i * m + j] <- 0;
      for u64 k <- 0 .. m {
        dest[i * m + j] <- dest[i * m + j] + a[i * m + k] * b[k * m + j]
      }
    }
  }
}

i32 main() {
  /* pas encore de création de tableaux */
  return 0
}