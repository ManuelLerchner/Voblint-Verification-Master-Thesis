#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int i = 6;
  i = i - 2;
  while (i != 0) {
    __goblint_check(i > 0);
    i = i - 2;
  }
  return 0;
}
