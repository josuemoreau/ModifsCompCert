#include <stdio.h>

#define ull unsigned long long
#define ll long long

extern void mul_matrix(ll* a, ll* b, ll* dest, ull m, ull n, ull p);

void print_matrix(ll a[], ull m, ull n) {
  for (ull i = 0; i < m; i++) {
    for (ull j = 0; j < n; j++)
      printf("%3lld ", a[i * n + j]);
    printf("\n");
  }
}

void print_line() { printf("\n"); }

int main() {
  ll a[] = {2, -1, 5, 6,
            3, 0, -4, 9,
            1, 0, 2, 4};
  ll b[] = {7, 9,
            0, -1,
            1, -3,
            -8, 2};
  ll c[] = {0, 0,
            0, 0,
            0, 0};
  mul_matrix(a, b, c, 3, 4, 2);
  print_matrix(a, 3, 4);
  printf("*\n");
  print_matrix(b, 4, 2);
  printf("=\n");
  print_matrix(c, 3, 2);
  return 0;
}
