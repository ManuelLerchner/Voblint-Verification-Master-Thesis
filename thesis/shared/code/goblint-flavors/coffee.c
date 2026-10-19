#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = 0;
  if (x >= 0) { y = x; } else { y = -x; }
  if (y >= 1) { __goblint_check(x != 0); }
  return 0;
}
