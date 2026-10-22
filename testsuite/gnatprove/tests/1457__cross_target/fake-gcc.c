/* Minimal stand-in for a cross compiler driver: GNATprove only queries it for
   its target name, so reporting one is enough. */

#include <stdio.h>
#include <string.h>

int main (int argc, char **argv)
{
  if (argc > 1 && strcmp (argv[1], "-dumpmachine") == 0)
    {
      puts ("arm-eabi");
      return 0;
    }
  return 1;
}
