all: build

build: force
	mkdir -p obj
	gprbuild -j0 -P gnatprove.gpr

PROD=-XBuild=Production

nightly: force
	mkdir -p obj
	gprbuild -j0 -P gnatprove.gpr $(PROD)
force:

clean:
	rm -rf obj
