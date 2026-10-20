#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int f(int i);
int g(int i) { int r; if (i == 0) return 1; if (0 < i) { r = f(i + 1); return r; } return 11; }
int f(int i) { int r1, r2; if (i == 0) return 2; if (0 < i) { r1 = g(i - 2); r2 = g(i - 3); return r1 + r2; } return 12; }
int main(void) {
  int a = f(0); __goblint_check(a == 2);
  int b = f(7); __goblint_check(b == 101);
  int c = f(9); __goblint_check(c == 265);
  int d = f(10); __goblint_check(d == 429);
  int e = g(0); __goblint_check(e == 1);
  int h = g(3); __goblint_check(h == 25);
  int k = g(6); __goblint_check(k == 101);
  int l = g(8); __goblint_check(l == 265);
  int m = f(13); __goblint_check(m == 1817);
  int n = f(20); __goblint_check(n == 52756);
  int o = g(13); __goblint_check(o == 2940);
  int p = g(20); __goblint_check(p == 85361);
  return 0;
}
