#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int i = 0;
  while (i < 10) { i = i + 1; }
  __goblint_check(i == 10);
  return 0;
}
