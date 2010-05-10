#include "sat.h"
int add (int x, int y) {
   if (x + y < 10000)
      return x + y;
   else
      return 10000;
}

int mult (int x, int y) {
   if (x * y < 10000)
      return x * y;
   else
      return 10000;
}