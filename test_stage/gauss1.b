i32 search_max_abs(u64 N, u32 n, u32 m, f64[N] A, u32 r, u32 j) {
  i32 k <- -1i32;
  f64 max <- 0.;
  for u32 i <- r .. n {
    if A[i * m + j] > max {
      k <- (i32) i;
      max <- A[i * m + j]
    } else if - A[i * m + j] > max {
      k <- (i32) i;
      max <- - A[i * m + j]
    }
  }
  return k
}

void divide_line_by_const(u64 N, u32 m, mut f64[N] A, u32 i, f64 k) {
  for u32 j <- 0 .. m {
    A[i * m + j] <- A[i * m + j] / k
  }
}

void exchange_lines(u64 N, u32 m, mut f64[N] A, u32 l1, u32 l2) {
  f64 tmp <- 0.;
  for u32 j <- 0 .. m {
    tmp <- A[l1 * m + j];
    A[l1 * m + j] <- A[l2 * m + j];
    A[l2 * m + j] <- tmp
  }
}

void add_lines(u64 N, u32 m, mut f64[N] A, u32 l1, f64 k, u32 l2) {
  for u32 j <- 0 .. m {
    A[l1 * m + j] <- A[l1 * m + j] + k * A[l2 * m + j]
  }
}

void gauss(u64 N, u32 n, u32 m, mut f64[N] A) {
  u32 r <- 0;
  f64 c <- 0.;
  for u32 j <- 0 .. m {
    i32 x <- search_max_abs(N, n, m, A, r, j);
    if (x = -1i32) { break }
    u32 k <- (u32) x;
    if A[k * m + j] != 0. {
      c <- A[k * m + j];
      divide_line_by_const(N, m, A, k, c);
      if k != r {
        exchange_lines(N, m, A, k, r)
      }
      for u32 i <- 0 .. n {
        if i != r {
          c <- - A[i * m + j];
          add_lines(N, m, A, i, c, j)
        }
      }
      r <- r + 1
    }
  }
}
