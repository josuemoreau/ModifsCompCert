#include <stdio.h>
#include <assert.h>

extern unsigned long search_max_abs(unsigned long long, unsigned long, unsigned long, double*, unsigned long, unsigned long);
extern void gauss(unsigned long long, unsigned long, unsigned long, double*);

void print_matrix(unsigned long n, unsigned long m, double* A) {
  assert(m > 0);
  for (unsigned long i = 0; i < n; i++) {
    printf("[");
    for (unsigned long j = 0; j < m - 1; j++)
      printf("%9.6g ", A[i * m + j]);
    printf("%9.6g]\n", A[i * m + (m - 1)]);
  }
}

int main() {
  double A1[] = { 8.0, 2.5, 3.0, 0.1,
                  3.1, 6.7, 2.2, 7.2,
                  4.0, 0.0, 9.4, 3.1 };

  double A2[] = { 8.0, 3.1, 4.0,
                  2.5, 6.7, 0.0,
                  3.0, 2.2, 9.4,
                  0.1, 7.2, 3.1 };

  double A3[] = {  2., -1.,  0.,
                  -1.,  2., -1.,
                   0., -1.,  2. };

  double A4[] = {  2., -1.,  0.,
                  -1.,  2., -1.,
                   0.,  3., -2. };

  print_matrix(3, 4, A1);
  gauss(12, 3, 4, A1);
  printf("--\n");
  print_matrix(3, 4, A1);
  printf("-------------------------------------\n");

  print_matrix(4, 3, A2);
  gauss(12, 4, 3, A2);
  printf("--\n");
  print_matrix(4, 3, A2);
  printf("-------------------------------------\n");

  print_matrix(3, 3, A3);
  gauss(9, 3, 3, A3);
  printf("--\n");
  print_matrix(3, 3, A3);
  printf("-------------------------------------\n");

  print_matrix(3, 3, A4);
  gauss(9, 3, 3, A4);
  printf("--\n");
  print_matrix(3, 3, A4);
  printf("-------------------------------------\n");

  return 0;
}