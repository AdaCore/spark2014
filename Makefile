# This Makefile is used to build and install GNATprove and its sub-components,
# at the exception of prover CVC4, which should be separately built/installed.
#
# To build gnat2why, you need:
#  . a working GNAT compiler
#  . a symbolic link in gnat2why/gnat_src that points to the GNAT sources
#  . an installation of the gnatcoll library
#
# To build gnatprove, you need:
#  . an installation of the gnatcoll library
#  . local checked out repositories of submodules why3 and alt-ergo.
#
# The necessary steps to correctly install gnat2why/gnatprove are
#
# 1) make setup
#
#    This does the local setup of submodules why3 and alt-ergo.
#
# 2) make
#
#    This builds gnatprove, gnat2why, why3 and alt-ergo.
#
# 3) make install-all
#
#    This copies all the necessary files into the install/ subdirectory, for
#    gnatprove, gnat2why, why3 and alt-ergo.
#
# 4) export PATH=/path/to/spark2014/install/bin:$PATH
#
#    This puts the directory install/bin in your path.

.PHONY: clean doc gnat2why gnat2why-nightly gnatprove install \
	install-all why3 alt-ergo all setup all-nightly doc-nightly

INSTALLDIR=$(CURDIR)/install
SHAREDIR=$(INSTALLDIR)/share
EXAMPLESDIR=$(SHAREDIR)/examples/spark
DOCDIR=$(SHAREDIR)/doc/spark
GNATPROVEDIR=$(SHAREDIR)/spark
CONFIGDIR=$(GNATPROVEDIR)/config
THEORIESDIR=$(GNATPROVEDIR)/theories
DOC=ug lrm

CP=cp -pr
GNATMAKE=gnatmake

# main target for developers
all: gnat2why gnatprove why3 alt-ergo

# main target for nightly builds
all-nightly: gnat2why-nightly gnatprove-nightly install install-examples

# Setup and installation of why3 and alt-ergo
# ===========================================
#
# We deal differently with submodules for why3 and alt-ergo in a developer
# setting, who builds directly why3 and alt-ergo, and for nightly builds, where
# the builds of why3 and alt-ergo are handled separately.
#
# Thus, special targets are defined for the developer only:
#   setup        setup of why3 and alt-ergo
#   install-all  install of gnatprove, why3 and alt-ergo

setup:
	cd why3 && ./configure --prefix=$(INSTALLDIR) --enable-relocation --disable-gui --disable-coq-libs --enable-coq-tactic=no
	cd alt-ergo && ./configure --prefix=$(INSTALLDIR)

why3:
	$(MAKE) -C why3

alt-ergo:
	$(MAKE) -C alt-ergo

install-all:
	$(MAKE) install
	$(MAKE) -C why3 install_spark2014
	$(MAKE) -C alt-ergo install

install:
	mkdir -p $(INSTALLDIR)/bin $(CONFIGDIR) $(THEORIESDIR)
	@echo "generating default target.atp in $(INSTALLDIR)/bin:"
	$(GNATMAKE) -q -c -u -gnats spark2014vsn.ads \
	  -gnatet=$(INSTALLDIR)/bin/target.atp
	$(CP) share/spark/config/*cgpr $(CONFIGDIR)
	$(CP) share/spark/theories/*why $(THEORIESDIR)
	$(CP) share/spark/theories/*mlw $(THEORIESDIR)

doc: $(DOC)

doc-nightly: $(DOC)
	cd docs/ug; $(MAKE) generate-nightly

$(DOC):
	$(MAKE) -C docs/$@ latexpdf LATEXOPTS="-interaction=nonstopmode"
	$(MAKE) -C docs/$@ html
	mkdir -p $(DOCDIR)/pdf
	mkdir -p $(DOCDIR)/html/$@
	$(CP) docs/$@/_build/latex/*.pdf $(DOCDIR)/pdf
	$(CP) docs/$@/_build/html/* $(DOCDIR)/html/$@
	$(MAKE) -C docs/$@ clean

gnat2why-nightly:
	$(MAKE) -C gnat2why/why/xgen
	$(MAKE) -C gnat2why AUTOMATED=1

gnat2why:
	$(MAKE) -C gnat2why/why/xgen
	$(MAKE) -C gnat2why

coverage:
	$(MAKE) -C gnat2why/why/xgen
	$(MAKE) -C gnat2why coverage
	cd gnat2why/testsuite; ./run-tests -j 5

gnatprove:
	$(MAKE) -C gnatprove build

gnatprove-nightly:
	$(MAKE) -C gnatprove nightly

install-examples:
	mkdir -p $(EXAMPLESDIR)
	for dir in `grep -v "^--" MANIFEST.examples` ; do \
	   $(CP) testsuite/gnatprove/tests/$$dir $(EXAMPLESDIR); \
	done
	find $(EXAMPLESDIR) -name test.py -exec rm -f {} \;
	find $(EXAMPLESDIR) -name test.out -exec rm -f {} \;

clean:
	$(MAKE) -C gnat2why/why/xgen clean
	$(MAKE) -C gnat2why clean
	$(MAKE) -C gnatprove clean
	$(MAKE) -C docs/ug clean
	$(MAKE) -C docs/lrm clean
	$(MAKE) -C why3 clean
	$(MAKE) -C alt-ergo clean
