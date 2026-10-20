#include <goblint.h>
extern int __VERIFIER_nondet_int(void);
int num_iterat;
int rec(void) {
  int res;
  if (0 < num_iterat) {
    num_iterat = num_iterat + 1;
    res = rec();
    __goblint_check(res == 5);
    return res;
  } else {
    if (num_iterat == 0) return 5; else return 2;
  }
}
int main(void) {
  num_iterat = 2;
  int r = rec();
  __goblint_check(r == 5);
  return 0;
}
