#include <stdio.h>
#include <stdlib.h>

extern void fadd(long long *, long long *, long long *, long long int);
extern void fmulmatrix(long long *, long long *, long long *, long long int);

void test1() {
  long long int a[3] = {1, 2, 3};
  long long int b[3] = {1, 1, 1};
  long long int c[3] = {0, 0, 0};

  /* *(c + 2) = 4; */

  printf("Test1\n");

  printf("a = ");
  for (int i = 0; i < 3; i++)
    printf ("%d ", a[i]);
  printf("\n");

  printf("b = ");
  for (int i = 0; i < 3; i++)
    printf ("%d ", b[i]);
  printf("\n");

  printf("c = ");
  for (int i = 0; i < 3; i++)
    printf ("%d ", c[i]);
  printf("\n");

  fadd(a, b, c, 3);

  printf("---------------------\n");

  printf("a = ");
  for (int i = 0; i < 3; i++)
    printf ("%d ", a[i]);
  printf("\n");

  printf("b = ");
  for (int i = 0; i < 3; i++)
    printf ("%d ", b[i]);
  printf("\n");

  printf("c = ");
  for (int i = 0; i < 3; i++)
    printf ("%d ", c[i]);
  printf("\n");
}

void test2() {
  long long int a[9] = {-3, 1, -4, 1, -5, 9, -2, 6, -5};
  long long int b[9] = {0, -1, 1, -2, 3, -5, 8, -13, 21};
  long long int c[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};

  printf("Test2\n");

  printf("a = \n");
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++)
      printf ("%d ", a[3 * i + j]);
    printf("\n");
  }
  printf("\n");

  printf("b = \n");
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++)
      printf ("%d ", b[3 * i + j]);
    printf("\n");
  }
  printf("\n");

  printf("c = \n");
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++)
      printf ("%d ", c[3 * i + j]);
    printf("\n");
  }
  printf("\n");

  fmulmatrix(a, b, c, 3);

  printf("---------------------\n");

  printf("a = \n");
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++)
      printf ("%d ", a[3 * i + j]);
    printf("\n");
  }
  printf("\n");

  printf("b = \n");
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++)
      printf ("%d ", b[3 * i + j]);
    printf("\n");
  }
  printf("\n");

  printf("c = \n");
  for (int i = 0; i < 3; i++) {
    for (int j = 0; j < 3; j++)
      printf ("%d ", c[3 * i + j]);
    printf("\n");
  }
  printf("\n");
}

int main (int argc, char** argv) {
  test1();
  test2();

  return 0;
}
