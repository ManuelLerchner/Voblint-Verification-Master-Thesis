#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int f(int j) { return j + 1; }
int main(void) {
  int i = 0, t;
  while (i < 10) { t = f(i); i = 1 + t; }
  __goblint_check(i == 10);
  return 0;
}
