void eratosthene(mut bool[N] prime, u64 N) {
  /* On aimerait ici un moyen de dire N >= 2 */
  if N < 2 return;
  prime[0u32] <- false;
  prime[1u32] <- false;
  for u64 k <- 2 .. N step 2 {
    prime[k] <- false
  }
  u64 i <- 3;
  while (i * i < N) {
    if prime[i] {
      for u64 j <- i .. N / i step 2 {
        prime[i * j] <- false
      }
    }
    i <- i + 1
  }
}