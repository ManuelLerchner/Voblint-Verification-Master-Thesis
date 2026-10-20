#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int f(int x, int y) { int r; if (x == 0) return y; r = f(x - 1, y - 1); return r; }
int main(void) {
  int a = f(8, 8); __goblint_check(a == 0);
  int b = f(20, 20); __goblint_check(b == 0);
  int c = f(300, 300); __goblint_check(c == 0);
  return 0;
}
