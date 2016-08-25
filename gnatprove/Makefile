all: setup build

setup:
	mkdir -p obj
	for f in `cat MANIFEST.gnat_minimal`; do \
	   cp ../gnat2why/gnat_src/$$f obj; \
	done

build: force
	gprbuild -j0 -P gnatprove.gpr

PROD=-XBuild=Production

nightly: force
	gprbuild -j0 -P gnatprove.gpr $(PROD)

force:

clean:
	rm -rf obj
