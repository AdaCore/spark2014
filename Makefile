# This Makefile is used to build gnat2why and gnatprove, and to install these
# tools.
#
# To build gnat2why, you need a working GNAT compiler and a symbolic link in
# gnat2why/gnat_src that points to the GNAT sources.
#
# To build gnatprove, you additionnally need an installation of the gnatcoll
# library, and local checked out repositories of submodules why3 and alt-ergo.
#
# To build gnatmerge, you additionnally need python support in gnatcoll and
# an installation of ASIS.
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
#    gnatprove, why3 and alt-ergo.
#
# 4) Put the directory install/bin in your path:
#	export PATH=<path_to_hilite_repo>/install/bin:$PATH

.PHONY: clean doc gnat1why gnat2why gnatprove install \
	install-all gnatmerge why3 alt-ergo all setup all-nightly doc-nightly

ADAINCLUDE=$(strip $(shell gnatls -v | grep adainclude))
GNAT_ROOT=$(shell echo $(ADAINCLUDE) | sed -e 's!\(.*\)/lib/gcc/\(.*\)!\1!')
INSTALLDIR=$(CURDIR)/install
SHAREDIR=$(INSTALLDIR)/share
EXAMPLESDIR=$(SHAREDIR)/examples/spark
DOCDIR=$(SHAREDIR)/doc/spark
GNATPROVEDIR=$(SHAREDIR)/spark
CONFIGDIR=$(GNATPROVEDIR)/config
THEORIESDIR=$(GNATPROVEDIR)/theories
DOC=ug lrm

CP=cp -pr

# main target for developers
all: gnat2why gnatprove why3 alt-ergo

# main target for nightly builds
all-nightly: gnat1why gnatprove-nightly install install-examples

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
	cd why3 && ./configure --prefix=$(INSTALLDIR) --enable-relocation --disable-gui
	cd alt-ergo && ./configure --prefix=$(INSTALLDIR)

why3:
	$(MAKE) -C why3

alt-ergo:
	$(MAKE) -C alt-ergo

install-all:
	$(MAKE) install
	$(MAKE) -C why3 install
	$(MAKE) -C alt-ergo install

install:
	mkdir -p $(CONFIGDIR)
	mkdir -p $(THEORIESDIR)
	$(CP) share/spark/config/*cgpr $(CONFIGDIR)
	$(CP) share/spark/theories/*why $(THEORIESDIR)
	$(CP) share/spark/theories/*mlw $(THEORIESDIR)

doc: $(DOC)

doc-nightly: $(DOC)
	cd docs/ug; $(MAKE) generate-nightly

$(DOC):
	echo x | $(MAKE) -C docs/$@ latexpdf
	$(MAKE) -C docs/$@ html
	mkdir -p $(DOCDIR)/pdf
	mkdir -p $(DOCDIR)/html/$@
	$(CP) docs/$@/_build/latex/*.pdf $(DOCDIR)/pdf
	$(CP) docs/$@/_build/html/* $(DOCDIR)/html/$@
	$(MAKE) -C docs/$@ clean

gnat1why:
	$(MAKE) -C gnat2why/why/xgen
	$(MAKE) -C gnat2why gnat1 gnat2why

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

gnatmerge:
	$(MAKE) -C gnatmerge

install-gnatmerge:
	$(MAKE) -C gnatmerge INSTALLDIR=$(INSTALLDIR) install

install-examples:
	mkdir -p $(EXAMPLESDIR)
	for dir in `grep -v "^--" MANIFEST.examples` ; do \
	   $(CP) testsuite/gnatprove/tests/$$dir $(EXAMPLESDIR); \
	done

clean:
	$(MAKE) -C gnat2why/why/xgen clean
	$(MAKE) -C gnat2why clean
	$(MAKE) -C gnatprove clean
	$(MAKE) -C docs/ug clean
	$(MAKE) -C docs/lrm clean
	$(MAKE) -C why3 clean
	$(MAKE) -C alt-ergo clean

# Translating the standard library for GNATprove
# ==============================================
#
# This applies gnat2why to the standard GNAT library. This is only used for debug.

STDLIB_TMP=stdlib_tmp

stdlib:
	rm -rf $(STDLIB_TMP)
	mkdir -p $(STDLIB_TMP)
	$(CP) Makefile.libprove $(STDLIB_TMP)
	$(MAKE) -C $(STDLIB_TMP) -f Makefile.libprove ROOT=$(GNAT_ROOT)

# "make stdlib-check" will run why on all Why files of the standard library,
# to detect problems with the translation to Why

stdlib-check:
	$(MAKE) -C $(STDLIB_TMP) -f Makefile.libprove ROOT=$(GNAT_ROOT) check
