all: setup build

setup:
	mkdir -p obj
	for f in `cat MANIFEST.gnat_minimal`; do \
	   cp ../gnat2why/gnat_src/$$f obj; \
	done

build:
	gprbuild -j0 -P gnatprove.gpr

PROD=-XBuild=Production

nightly:
	gprbuild -j0 -P gnatprove.gpr $(PROD)

clean:
	gprclean -P gnatprove.gpr -r
	rm -rf obj
