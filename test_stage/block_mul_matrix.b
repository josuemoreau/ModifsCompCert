u64 min(u64 a, u64 b) {
  if a < b { return a } else { return b }
}

void block_mul_matrix(i64[m, n] a, i64[n, p] b, mut i64[m, p] dest,
                      u64 m, u64 n, u64 p, u64 bs) {
  i64 s <- 0;
  for u64 I <- 0 .. m step bs {
    u64 I1 <- I + bs;
    u64 I2 <- min(m, I1);
    for u64 J <- 0 .. p step bs {
      u64 J1 <- J + bs;
      u64 J2 <- min(p, J1);
      for u64 K <- 0 .. n step bs {
        u64 K1 <- K + bs;
        u64 K2 <- min(n, K1);
        for u64 i <- I .. I2
          for u64 j <- J .. J2 {
            s <- 0;
            for u64 k <- K .. K2 {
              s <- s + a[i, k] * b[k, j]
            }
            dest[i, j] <- dest[i, j] + s
          }
      }
    }
  }
}
