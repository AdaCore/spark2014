#include "rnd.h"
#include <stdio.h>

FILE *devrandom;

void init()
{
  devrandom = fopen("/dev/random", "r");
}

void get_random(uint32_t *data)
{
  fread(data, 1, 4, devrandom);
}
