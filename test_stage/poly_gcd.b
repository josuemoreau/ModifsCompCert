/* On représente un polynôme pas son tableau de coefficients */

bool is_zero(f64[D] A, u64 D) {
  for u64 i <- 0 .. D {
    if A[i] != 0. { return false }
  }
  return true
}

u64 deg(f64[DA] A, u64 DA) {
  u64 i <- DA - 1;
  while i >= 0 {
    if A[i] != 0. {
      return i
    }
  }
  return -1u64
}

f64 quotient(f64[DA] A, f64[DB] B, u64 DA, u64 DB) {
  u64 da <- deg(A, DA);
  u64 db <- deg(B, DB);
  if da < db {
    return 0
  } else {
    return A[da] / B[db]
  }
}

void comb_lin(mut f64[DA] A, f64[DB] B, f64 x, u64 DA, u64 DB) {
  for u64 i <- 0 .. DA {
    A[i] <- A[i] + x * B[i]
  }
}

void gcd(f64[DA] A, f64[DB] B, u64 DA, u64 DB) {
  bool isz <- is_zero(B, DB);
  if !isz {
    f64 x <- 0.5;
    comb_lin(A, B, x, DA, DB)
  }
}