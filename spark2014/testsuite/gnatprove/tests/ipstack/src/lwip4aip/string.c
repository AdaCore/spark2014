#include <string.h>

size_t
strlen (const char* s) {
  int len = 0;
  while (s[len])
    len++;
  return len;
}

char *
strncpy(char * dst, const char * src, size_t len) {
   int i = 0;

   while (src[i] && i < len) {
      dst[i] = src[i];
      i++;
   }

   while (i < len)
      dst[i++] = '\0';

   return dst;
}
