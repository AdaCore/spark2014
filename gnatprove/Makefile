all: setup build

setup:
	mkdir -p obj

build:
	gprbuild -j0 -P gnatprove.gpr

PROD=-XBuild=Production

nightly:
	gprbuild -j0 -P gnatprove.gpr $(PROD)

clean:
	gprclean -P gnatprove.gpr -r
