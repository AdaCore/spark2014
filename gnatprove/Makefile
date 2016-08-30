# need to define this variable here, to allow overriding it when calling the
# Makefile
PROD=

all: build

build:
	gprbuild -p -j0 -P gnatprove.gpr $(PROD)

clean:
	gprclean -P gnatprove.gpr -r
	rm -rf obj
