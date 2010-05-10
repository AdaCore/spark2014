.PHONY: test

test:
	gcc -c *.c
	gcc -o test *.o
	./test

frama-c:
	frama-c -jessie sat.c
	frama-c -jessie pricing.c
