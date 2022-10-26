extern unsigned int __compcert_va_int32(void *);
extern unsigned long long __compcert_va_int64(void *);
extern double __compcert_va_float64(void *);
extern void *__compcert_va_composite(void *, unsigned long long);
extern long long __compcert_i64_dtos(double);
extern unsigned long long __compcert_i64_dtou(double);
extern double __compcert_i64_stod(long long);
extern double __compcert_i64_utod(unsigned long long);
extern float __compcert_i64_stof(long long);
extern float __compcert_i64_utof(unsigned long long);
extern long long __compcert_i64_sdiv(long long, long long);
extern unsigned long long __compcert_i64_udiv(unsigned long long, unsigned long long);
extern long long __compcert_i64_smod(long long, long long);
extern unsigned long long __compcert_i64_umod(unsigned long long, unsigned long long);
extern long long __compcert_i64_shl(long long, int);
extern unsigned long long __compcert_i64_shr(unsigned long long, int);
extern long long __compcert_i64_sar(long long, int);
extern long long __compcert_i64_smulh(long long, long long);
extern unsigned long long __compcert_i64_umulh(unsigned long long, unsigned long long);
extern void __builtin_debug(int, ...);
void f(int *, int *, int *, int);
int main(int, signed char **);
void f(int *a, int *b, int *c, int n)
{
  /*skip*/;
}

int main(int argc, signed char **argv)
{
  int a[3];
  int b[3];
  int c[3];
  *(a + 0) = 1;
  *(a + 1) = 2;
  *(a + 2) = 3;
  *(b + 0) = 1;
  *(b + 1) = 1;
  *(b + 2) = 1;
  *(c + 0) = 0;
  *(c + 1) = 0;
  *(c + 2) = 0;
  f(a, b, c, 3);
  return 0;
  return 0;
}


