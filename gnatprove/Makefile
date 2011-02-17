all: build

build: force
	mkdir -p obj
	gnatmake -P gnatprove.gpr

force:

clean:
	rm -rf obj

tags: force
	gnatxref -f -aO obj gnatprove.gpr | parse_xref > tags
