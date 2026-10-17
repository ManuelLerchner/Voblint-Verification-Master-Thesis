#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int x = -5;
  int y = -10;
  int z = x + y;
  __goblint_check(z < 0);
  return 0;
}
