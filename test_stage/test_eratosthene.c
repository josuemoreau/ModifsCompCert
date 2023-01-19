#include <stdio.h>
#include <assert.h>

extern void eratosthene(char*, unsigned long long);

void print_prime_array(char* prime, unsigned long long sz) {
  for (int i = 0; i < sz; i++)
    if (prime[i])
      printf("%d ", i);
  printf("\n");
}

int count_prime_numbers(char* prime, unsigned long long sz) {
  int cnt = 0;
  for (int i = 0; i < sz; i++)
    if (prime[i])
      cnt++;
  return cnt;
}

#define N 100

int main() {
  char prime[N];
  for (int i = 0; i < N; i++)
    prime[i] = 1;
  eratosthene(prime, N);
  print_prime_array(prime, N);
  printf("%d prime numbers < %d.\n", count_prime_numbers(prime, N), N);
  return 0;
}