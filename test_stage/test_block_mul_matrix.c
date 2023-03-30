#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define ull unsigned long long
#define ll long long

extern void block_mul_matrix(ll* a, ll* b, ll* dest, ull m, ull n, ull p, ull bs);
extern void mul_matrix(ll* a, ll* b, ll* dest, ull m, ull n, ull p);

void print_matrix(ll a[], ull m, ull n) {
  for (ull i = 0; i < m; i++) {
    for (ull j = 0; j < n; j++)
      printf("%3lld ", a[i * n + j]);
    printf("\n");
  }
}

void print_line() { printf("\n"); }

void test_random(ull m, ull n, ull p, ull bs, ll is) {
  srand(time(NULL));
  ll* a = malloc(sizeof(ll) * m * n);
  ll* b = malloc(sizeof(ll) * n * p);
  ll* c1 = malloc(sizeof(ll) * m * p);
  ll* c2 = malloc(sizeof(ll) * m * p);
  for (ull i = 0; i < m; i++)
    for (ull j = 0; j < n; j++)
      for (ull k = 0; k < p; k++) {
        a[i * n + j] = (ll)rand() % is;
        b[j * p + k] = (ll)rand() % is;
        c1[i * p + k] = 0;
        c2[i * p + k] = 0;
      }
  block_mul_matrix(a, b, c1, m, n, p, bs);
  print_matrix(a, m, n);
  printf("*\n");
  print_matrix(b, n, p);
  printf("=\n");
  print_matrix(c1, m, p);
  printf("------------------------------------\n");
  mul_matrix(a, b, c2, m, n, p);
  /* print_matrix(c2, m, p); */
  for (ull i = 0; i < m; i++)
    for (ull k = 0; k < p; k++)
      if (c1[i * p + k] != c2[i * p + k]) {
        printf("Block and naive matrix multiplication doesn't have the same result.\n");
        abort();
      }
  printf("OK\n");
}

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
  block_mul_matrix(a, b, c, 3, 4, 2, 2);
  print_matrix(a, 3, 4);
  printf("*\n");
  print_matrix(b, 4, 2);
  printf("=\n");
  print_matrix(c, 3, 2);

  test_random(15, 20, 21, 4, 100000);

  return 0;
}
