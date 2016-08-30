all: build

build:
	gprbuild -p -j0 -P gnatprove.gpr

PROD=-XBuild=Production

nightly:
	gprbuild -p -j0 -P gnatprove.gpr $(PROD)

clean:
	gprclean -P gnatprove.gpr -r
	rm -rf obj
