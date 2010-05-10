#include "pricing.h"
#include <stdio.h>

int main() {
  Item b[] = { { 10, 1 } };
  int p = price_of_basket (b, 1);
  printf ("Price of basket is %d\n", p);
  return 0;
}
