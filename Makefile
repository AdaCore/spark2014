.PHONY: clean doc gnat1why gnat2why gnatprove stdlib install-stdlib

DOC=install/share/doc/gnatprove
TMP=stdlib_tmp
GNAT_ROOT=/usr/gnat

all: gnat2why gnatprove

all-nightly: gnat1why gnatprove stdlib install-stdlib

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

stdlib:
	rm -rf $(TMP)
	mkdir -p $(TMP)
	cp Makefile.libprove $(TMP)
	$(MAKE) -C $(TMP) -f Makefile.libprove ROOT=$(GNAT_ROOT)

install-stdlib:
	cp $(TMP)/*.ali $(TMP)/*__types_vars_spec.mlw \
           $(TMP)/*__types_vars_body.mlw $(TMP)/*__subp_spec.mlw $(WHYLIB)

clean:
	$(MAKE) -C gnat_backends/why clean
	$(MAKE) -C gnatprove clean
	$(MAKE) -C docs/ug clean
