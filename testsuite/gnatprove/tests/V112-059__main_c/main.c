#include <stdio.h>
extern void adainit(void);
extern void adafinal(void);
extern int _ada_square(int arg);
int main(int argc, char **argv)
{
	adainit();
	for (int i = 1; i <= 4; ++i) {
		int result = _ada_square(i);
		printf("The square of %d is %d\n", i, result);
	}
	adafinal();
	return 0;
}
