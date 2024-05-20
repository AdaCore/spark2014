#include <stdio.h>

extern
void os_exit() {}

typedef struct {
  int a;
  char b;
  unsigned char c;
  short d;
} c_struct;

extern
void update_c_struct(c_struct* arg) {
  arg->a = 42;
  arg->b = 'c';
  arg->c = 42;
  arg->d = 42;
}

extern
int read_c_struct(const c_struct* arg);

extern
void init(const c_struct* arg);

int main() {
  c_struct s = { 0, 'b', 0, 0 };
  init(&s);
  printf ("s = {%d,%c,%d,%d}\n", s.a, s.b, s.c, s.d);
  printf ("s.a = %d\n", read_c_struct(&s));
  return 0;
}
