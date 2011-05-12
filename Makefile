.PHONY: clean doc gnat1why gnat2why gnatprove

DOC=install/share/doc/gnatprove

all: gnat2why gnatprove doc

all-nightly: gnat1why gnatprove

doc:
	$(MAKE) -C docs/ug latexpdf
	$(MAKE) -C docs/ug html
	mkdir -p $(DOC)/pdf
	cp -p docs/ug/_build/latex/gnatprove_ug.pdf $(DOC)/pdf
	cp -pr docs/ug/_build/html $(DOC)

gnat1why:
	$(MAKE) -C gnat_backends/why gnat1 gnat2why

gnat2why:
	$(MAKE) -C gnat_backends/why

gnatprove:
	$(MAKE) -C gnatprove

clean:
	$(MAKE) -C gnat_backends/why clean
	$(MAKE) -C gnatprove clean
	$(MAKE) -C docs/ug clean
