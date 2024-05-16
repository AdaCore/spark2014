#ifndef _RND_H_
#define _RND_H_

#include <stdint.h>

/* Users must call init before any call to get_random */
void init();

/* Returns 32 bits of true random data */
void get_random(uint32_t *data);

#endif
