# This Makefile is used to build and install GNATprove and its
# sub-components, at the exception of provers CVC4 and Z3, which should be
# separately built/installed.
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
INCLUDEDIR=$(INSTALLDIR)/include/spark
LIBDIR=$(INSTALLDIR)/lib/gnat
EXAMPLESDIR=$(SHAREDIR)/examples/spark
DOCDIR=$(SHAREDIR)/doc/spark
GNATPROVEDIR=$(SHAREDIR)/spark
CONFIGDIR=$(GNATPROVEDIR)/config
THEORIESDIR=$(GNATPROVEDIR)/theories
RUNTIMESDIR=$(GNATPROVEDIR)/runtimes
DOC=ug lrm
# Control if gnatprove is built in production or debug mode
PROD=-XBuild=Production
CP=cp -pr
MV=mv -f
GNATMAKE=gnatmake
VERSION=0.0w

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
#   setup        why3, alt-ergo
#   install-all  install of gnatprove, why3 and alt-ergo

setup:
	cd why3 && ./configure --prefix=$(INSTALLDIR) \
		--enable-relocation \
		--enable-coq-tactic=no \
		--disable-menhirLib
	cd alt-ergo && ./configure --prefix=$(INSTALLDIR)

why3:
	$(MAKE) -C why3

alt-ergo:
	$(MAKE) -C alt-ergo

install-all:
	$(MAKE) install
	$(MAKE) -C why3 install_spark2014_dev
	$(MAKE) -C alt-ergo install
        # Move internal binaries to libexec/spark/bin like the nighty build
        # does (in anod scripts), as why3 executables expect this relative
        # location to find the Why3 installation files in share. Do this for
        # all internal binaries even if not strictly needed.
	mkdir -p install/libexec/spark/bin
	$(MV) install/bin/why3server install/libexec/spark/bin
	$(MV) install/bin/why3realize install/libexec/spark/bin
	$(MV) install/bin/gnatwhy3 install/libexec/spark/bin
	$(MV) install/bin/why3config install/libexec/spark/bin
	# the following line is allowed to fail - why3ide might not be
	# installed
	-$(MV) install/bin/why3ide install/libexec/spark/bin
	$(MV) install/bin/alt-ergo install/libexec/spark/bin
        # Create the fake prover scripts to help extract benchmarks.
	$(CP) benchmark_script/fake_* install/libexec/spark/bin
        # It is ok for developers to not have a local build of CVC4. In that
        # case we don't want to have an error to be issued.
	$(MV) install/bin/cvc4 install/libexec/spark/bin 2> /dev/null || true

install:
	mkdir -p $(INSTALLDIR)/bin $(CONFIGDIR) $(THEORIESDIR) \
	  $(RUNTIMESDIR) $(INCLUDEDIR) $(LIBDIR)
	@echo "Generate default target.atp in $(INSTALLDIR)/bin:"
	$(GNATMAKE) -q -c -u -gnats spark2014vsn.ads \
	  -gnatet=$(INSTALLDIR)/bin/target.atp
	$(CP) share/spark/help.txt $(GNATPROVEDIR)
	$(CP) share/spark/config/* $(CONFIGDIR)
	$(CP) share/spark/theories/*why $(THEORIESDIR)
	$(CP) share/spark/theories/*mlw $(THEORIESDIR)
	$(CP) share/spark/runtimes/README $(RUNTIMESDIR)
	@echo "Generate Coq files by preprocessing context files:"
	$(MAKE) -C include generate
	$(CP) include/*.ad? $(INCLUDEDIR)
	$(CP) include/*.gpr $(LIBDIR)
	$(CP) include/proof $(LIBDIR)

doc: $(DOC)

doc-nightly: $(DOC)
	cd docs/ug; $(MAKE) generate-nightly VERSION=$(VERSION)

$(DOC):
	$(MAKE) -C docs/$@ latexpdf LATEXOPTS="-interaction=nonstopmode" VERSION=$(VERSION)
	$(MAKE) -C docs/$@ html VERSION=$(VERSION)
	mkdir -p $(DOCDIR)/pdf
	mkdir -p $(DOCDIR)/html/$@
	$(CP) docs/$@/_build/latex/*.pdf $(DOCDIR)/pdf
	$(CP) docs/$@/_build/html/* $(DOCDIR)/html/$@
	$(MAKE) -C docs/$@ clean

gnat2why-nightly:
	$(MAKE) -C gnat2why AUTOMATED=1 GPRARGS=$(PROD)

gnat2why:
	$(MAKE) -C gnat2why

coverage:
	$(MAKE) -C gnat2why coverage

gnatprove:
	$(MAKE) -C gnatprove build

gnatprove-nightly:
	$(MAKE) -C gnatprove build PROD=$(PROD)

install-examples:
	mkdir -p $(EXAMPLESDIR)
        # install examples from the testsuite as identified in file
        # MANIFEST.examples
	for dir in `grep -v "^--" MANIFEST.examples` ; do \
	   $(CP) testsuite/gnatprove/tests/$$dir $(EXAMPLESDIR); \
	done
	find $(EXAMPLESDIR) -name test.py -exec rm -f {} \;
	find $(EXAMPLESDIR) -name test.out -exec rm -f {} \;
        # install examples in GNATprove-by-Example section of User's Guide
        # a special example
	$(CP) docs/ug/gnatprove_by_example/examples \
	  $(EXAMPLESDIR)/gnatprove_by_example

clean:
	$(MAKE) -C gnat2why clean
	$(MAKE) -C gnatprove clean
	$(MAKE) -C docs/ug clean
	$(MAKE) -C docs/lrm clean
	$(MAKE) -C why3 clean
	$(MAKE) -C alt-ergo clean
	$(MAKE) -C include clean
        rm -f docs/sphinx_support/confvars.py
