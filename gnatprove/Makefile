all: build

build: force
	mkdir -p obj
	gnatmake -j0 -P gnatprove.gpr

PROD=-XBuild=Production

nightly: force
	mkdir -p obj
	gnatmake -j0 -P gnatprove.gpr $(PROD)
force:

clean:
	rm -rf obj

tags: force
	gnatxref -f -aO obj gnatprove.gpr | parse_xref > tags
