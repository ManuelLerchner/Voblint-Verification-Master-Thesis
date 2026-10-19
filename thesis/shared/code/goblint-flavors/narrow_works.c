#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int i = 0;
  while (1) {
    i = i + 1;
    if (i >= 10) { i = 0; }
    __goblint_check(i <= 9);
  }
  return 0;
}
