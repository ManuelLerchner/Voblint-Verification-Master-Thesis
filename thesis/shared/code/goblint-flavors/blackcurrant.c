#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int i = 0;
  int c;
  while (1) {
    c = __VERIFIER_nondet_int();
    if (c) {
      i = i + 1;
      if (i >= 10) { i = 0; }
    }
    __goblint_check(i <= 9);
  }
  return 0;
}
