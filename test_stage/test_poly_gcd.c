#include <stdio.h>

extern char is_zero(double*, unsigned long long);
extern long long deg(double*, unsigned long long);
extern void modulo(double*, double*, unsigned long long, unsigned long long);
extern void gcd(double*, double*, unsigned long long, unsigned long long);

void print_poly(double* A, unsigned long long DA, char* name) {
  printf("    ");
  for (int i = DA - 1; i > 1; i--)
    printf("         %d    ", i);
  printf("\n%1s = ", name);
  for (int i = DA - 1; i > 0; i--) {
    printf("%8.5gx   + ", A[i]);
  }
  printf("%8.5g\n", A[0]);
}

int main() {
  // double A[5] = {0., 2., 5., 3., 1.};
  // double B[2] = {1., 1.};

  double A[5] = {7. , 16.5 , 42., 39.5, 48.};
  double B[3] = {3.5,  1.25,  8.};
  double C[3] = { 6.,  7., 1.};
  double D[3] = {-6., -5., 1.};

  print_poly(A, 5, "A");
  printf("--------------------------------------------------------------------\n");
  print_poly(B, 3, "B");

  printf("--------------------------------------------------------------------\n");
  printf("deg A = %ld\n", deg(A, 5));
  printf("deg B = %ld\n", deg(B, 3));
  printf("--------------------------------------------------------------------\n");

  gcd(A, B, 5, 3);

  print_poly(A, 5, "A");
  printf("--------------------------------------------------------------------\n");
  print_poly(B, 3, "B");

  printf("\n\n\n");

  print_poly(C, 3, "C");
  printf("--------------------------------------------------------------------\n");
  print_poly(D, 3, "D");
  printf("--------------------------------------------------------------------\n");

  gcd(C, D, 3, 3);

  print_poly(C, 3, "C");
  printf("--------------------------------------------------------------------\n");
  print_poly(D, 3, "D");

  return 0;
}