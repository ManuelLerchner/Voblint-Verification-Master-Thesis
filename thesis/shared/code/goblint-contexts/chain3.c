#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int h(int i) { int r; if (i == 0) return 3; if (0 < i) { r = h(i - 1); return r; } return 13; }
int g(int i) { int r; if (i == 0) return 2; if (0 < i) { r = h(i - 1); return r; } return 12; }
int f(int i) { int r; if (i == 0) return 1; if (0 < i) { r = g(i - 1); return r; } return 11; }
int main(void) {
  int a = f(11); __goblint_check(a == 3);
  int b = g(12); __goblint_check(b == 3);
  int c = g(20); __goblint_check(c == 3);
  int d = f(20); __goblint_check(d == 3);
  int e = h(40); __goblint_check(e == 3);
  int x = h(300); __goblint_check(x == 3);
  int y = f(300); __goblint_check(y == 3);
  return 0;
}
