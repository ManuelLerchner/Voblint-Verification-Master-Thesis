#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int m;
int a(int i) { int r; if (i == 0) return 11; if (0 < i) { r = a(i - 1); return r; } return 1; }
int b(int i) { int r; if (i == 0) return 12; if (0 < i) { r = a(i - 1); return r; } return 2; }
int c(int i) { int r; if (i == 0) return 13; if (0 < i) { r = b(i - 1); return r; } return 3; }
int e(int i);
int f(int i) { int r; if (0 < i) { r = e(i - 1); return r; } return 2; }
int e(int i) { int r = f(i - 1); return r + 1; }
int h(int i) { int r; if (i == 0) return 1; if (0 < i) { r = h(i - 1); return r; } return 0; }
int k(int i) { int r; if (i == 2) { r = h(i - 1); return r + 1; } if (0 < i) { r = k(i - 1); return r; } return 1; }
int o(int i) { if (0 < i) { i = i - 1; m = i; o(i); } return 0; }
int main(void) {
  int x0 = a(7); __goblint_check(x0 == 11);
  int x1 = a(8); __goblint_check(x1 == 11);
  int x2 = c(11); __goblint_check(x2 == 11);
  int x3 = b(21); __goblint_check(x3 == 11);
  int y0 = e(5); __goblint_check(y0 == 5);
  int y1 = e(7); __goblint_check(y1 == 6);
  int z0 = k(9); __goblint_check(z0 == 2);
  int z1 = k(10); __goblint_check(z1 == 2);
  m = 20; o(5); __goblint_check(m == 0);
  m = 20; o(6); __goblint_check(m == 0);
  return 0;
}
