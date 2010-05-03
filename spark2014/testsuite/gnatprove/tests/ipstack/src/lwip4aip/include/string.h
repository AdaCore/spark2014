/*******************************
 *            IPStack          *
 *******************************
 * Copyright (C) 2010, AdaCore *
 *******************************/

#ifndef __STRING_H__
#define __STRING_H__

typedef unsigned int size_t;
extern void *memset(void *s, int c, size_t n);
extern void *memcpy(void *dest, const void *src, size_t n);
extern char *strncpy(char *dest, const char *src, size_t n);
extern size_t strlen (const char*);

#define NULL ((void*)0)

#endif
