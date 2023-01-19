/* On représente un polynôme pas son tableau de coefficients */

bool is_zero(f64[D] A, u64 D) {
  for u64 i <- 0 .. D {
    if A[i] != 0. { return false }
  }
  return true
}

i64 deg(f64[DA] A, u64 DA) {
  i64 i <- (i64) DA - 1;
  while i >= 0 {
    if A[i] != 0. {
      return i
    }
    i <- i - 1
  }
  return -1i64
}

void d_comb_lin(mut f64[DA] A, f64[DB] B, f64 x, i64 d, u64 DA, u64 DB) {
  i64 db <- deg(B, DB);
  if db >= 0 {
    for u64 i <- 0 .. ((u64) db + 1) {  
      A[d + (i64) i] <- A[d + (i64) i] + x * B[i]
    }
  }
}

void modulo(mut f64[DA] A, f64[DB] B, u64 DA, u64 DB) {
  i64 da <- deg(A, DA);
  i64 db <- deg(B, DB);
  if da >= 0 && db >= 0 {
    i64 i  <- da - db;
    f64 k  <- 0.;
    while i >= 0 {
      if A[i + db] = 0. { i <- i - 1; continue }
      k <- - (A[i + db] / B[db]);
      d_comb_lin(A, B, k, i, DA, DB);
      i <- i - 1
    }
  }
}

void gcd(mut f64[DA] A, mut f64[DB] B, u64 DA, u64 DB) {
  bool isz <- is_zero(B, DB);
  if !isz {
    modulo(A, B, DA, DB);
    gcd(B, A, DB, DA)
  }
}