# This Makefile is used to build and install GNATprove and its
# sub-components, at the exception of provers (CVC4, Z3, Alt-Ergo) which
# should be separately built/installed.
#
# To build gnat2why, you need:
#  . a working GNAT compiler
#  . a symbolic link in gnat2why/gnat_src that points to the GNAT sources
#  . an installation of the gnatcoll library
#
# To build gnatprove, you need:
#  . an installation of the gnatcoll library
#  . local checked out repositories of submodules why3.
#
# On cygwin, we suggest you work in a folder where cygwin and windows path are
# the same. You can achieve this by creating a folder e.g. C:\spark as a
# working space, and mounting it in cygwin by adding the following line to
# your /etc/fstab file:
#
#  c:/spark /spark ntfs binary,posix=0,noacl 0 0
#
# The necessary steps to correctly install gnat2why/gnatprove are
#
# 1) make setup
#
#    This does the local setup of submodule why3.
#
# 2) make
#
#    This builds gnatprove, gnat2why, and why3.
#
# 3) make install-all
#
#    This copies all the necessary files into the install/ subdirectory, for
#    gnatprove, gnat2why, and why3.
#
# 4) export PATH=/path/to/spark2014/install/bin:$PATH
#
#    This puts the directory install/bin in your path.

.PHONY: clean doc gnat2why gnat2why-nightly gnatprove install \
	install-all why3 all setup all-nightly doc-nightly run-benchmark \
        create-benchmark session_archive

COVERAGE_ROOT_DIR?=/it/wave/x86_64-linux/spark2014-core_assertions_coverage/src/
COVERAGE_SOURCE_DIR?=/it/wave/x86_64-linux/spark2014-core_assertions_coverage/src/

INSTALLDIR=$(CURDIR)/install
SHAREDIR=$(INSTALLDIR)/share
SIDDIR=$(SHAREDIR)/gnat2why-sids
INCLUDEDIR=$(INSTALLDIR)/include/spark
LIBDIR=$(INSTALLDIR)/lib/gnat
EXAMPLESDIR=$(SHAREDIR)/examples/spark
DOCDIR=$(SHAREDIR)/doc/spark
GNATPROVEDIR=$(SHAREDIR)/spark
CONFIGDIR=$(GNATPROVEDIR)/config
EXPLAINCODESDIR=$(GNATPROVEDIR)/explain_codes
THEORIESDIR=$(GNATPROVEDIR)/theories
RUNTIMESDIR=$(GNATPROVEDIR)/runtimes
DOC=ug lrm
# Control if gnatprove is built in production or debug mode
PROD=-XBuild=Production
CP=cp -pr
MV=mv -f
VERSION=0.0w

# main target for developers
all: gnat2why gnatprove why3

# main target for nightly builds
all-nightly: gnat2why-nightly gnatprove-nightly install install-examples
coverage-nightly: coverage gnatprove-nightly install install-coverage install-examples

# Setup and installation of why3
# ==============================
#
# We deal differently with submodules for why3 in a developer
# setting, who builds directly why3, and for nightly builds, where
# the builds of why3 and cvc4, z3, and alt-ergo are handled separately.
#
# Thus, special targets are defined for the developer only:
#   setup        why3
#   install-all  install of gnatprove and why3

setup:
	cd why3 && ./configure --prefix=$(INSTALLDIR)/libexec/spark \
		--enable-relocation --disable-js-of-ocaml \
		--disable-hypothesis-selection --disable-re --disable-coq-libs

why3:
	$(MAKE) -C why3 -j $(nproc)

install-all:
	$(MAKE) install
	$(MAKE) -C why3 install_spark2014_dev
	sha256sum $(INSTALLDIR)/libexec/spark/bin/gnatwhy3 | cut -d' ' -f1 > $(INSTALLDIR)/libexec/spark/bin/gnatwhy3.hash
	# Create the fake prover scripts to help extract benchmarks.
	$(CP) benchmark_script/fake_* $(INSTALLDIR)/libexec/spark/bin

install:
	mkdir -p $(INSTALLDIR)/bin $(CONFIGDIR) $(THEORIESDIR) \
	  $(EXPLAINCODESDIR) $(RUNTIMESDIR) $(INCLUDEDIR) $(LIBDIR)
	@echo "Generate default target.atp in $(INSTALLDIR)/bin:"
	gcc -c -gnats spark2014vsn.ads -gnatet=$(INSTALLDIR)/bin/target.atp
	$(CP) share/spark/help.txt $(GNATPROVEDIR)
	$(CP) share/spark/config/* $(CONFIGDIR)
	$(CP) share/spark/explain_codes/* $(EXPLAINCODESDIR)
	$(CP) share/spark/theories/*why $(THEORIESDIR)
	$(CP) share/spark/theories/*mlw $(THEORIESDIR)
	$(CP) share/spark/runtimes/README $(RUNTIMESDIR)
	@echo "Generate Coq files by preprocessing context files:"
	$(MAKE) -C include generate
	$(CP) include/src/*.ad? $(INCLUDEDIR)
	mkdir -p $(INCLUDEDIR)/full
	mkdir -p $(INCLUDEDIR)/light
	$(CP) include/src/full/*.ad? $(INCLUDEDIR)/full
	$(CP) include/src/light/*.ad? $(INCLUDEDIR)/light
	$(CP) include/*.gpr $(LIBDIR)
	$(CP) include/*.gpr.templ $(LIBDIR)
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
	# Produce Ada code that stores the reserved keywords of Why3
	# This script should be run *ONLY* in developer build not in prod
	# (gnat2why-nightly)
	python3 scripts/why3keywords.py why3/src/core/keywords.ml src/why/why-keywords.adb
	$(MAKE) -C gnat2why
	# (The timestamp of) src/why/xgen/gnat_ast.ml is updated every time `make` is called in
	# `gnat2why`, causing a recompilation of why3 every time because Why3's makefile is
	# based on timestamps not file content. So we check if anything changed before copying.
	SOURCE=src/why/xgen/gnat_ast.ml; TARGET=why3/plugins/gnat_json/gnat_ast.ml; \
	cmp "$$SOURCE" "$$TARGET" || $(CP) $$SOURCE $$TARGET

coverage:
	$(MAKE) -C gnat2why AUTOMATED=1 coverage GPRARGS=$(PROD)

install-coverage:
	rm -rf $(SIDDIR)
	mkdir $(SIDDIR)
	find gnat2why/obj -name '*.sid' -exec cp \{\} $(SIDDIR)/ \;

coverage-report:
	find $(COVERAGE_TRACES_DIR) -name "*.srctrace" > tracefiles

	# Look for SID files both in the installation tree given by the environment
	# (COVERAGE_SIDS_DIR, for testsuite runs in production) and in our own
	# object directory (for testsuite runs based on local builds).
	> sidfiles
	for dir in "$(COVERAGE_SIDS_DIR)" gnat2why/obj; do \
		if [ -d "$$dir" ]; then \
			find "$$dir" -name "*.sid" >> sidfiles; \
		fi; \
	done

	gnatcov coverage --level=stmt --annotate=cobertura --sid @sidfiles --source-root $(COVERAGE_ROOT_DIR) --output-dir=cobertura-report @tracefiles
	gnatcov coverage --level=stmt --annotate=dhtml --sid @sidfiles --source-rebase $(COVERAGE_ROOT_DIR)=$(COVERAGE_SOURCE_DIR) --output-dir=html-report @tracefiles

codepeer-run:
	$(MAKE) --no-print-directory -C gnat2why codepeer-run
	$(MAKE) --no-print-directory -f Makefile.gnatprove codepeer-run

codepeer: codepeer-run
	mkdir -p out
	gnatsas --version | tee out/version.out
	@echo "version:XFAIL:always fails" > out/results
	@$(MAKE) --no-print-directory -C gnat2why codepeer 2>&1 | tee out/codepeer.out
	@$(MAKE) --no-print-directory -f Makefile.gnatprove codepeer 2>&1 | tee --append out/codepeer.out
	@if [ -s out/codepeer.out ]; then \
	  echo "codepeer:FAILED:unexpected messages" >> out/results; \
	else \
	  echo "codepeer:PASSED" >> out/results; \
	fi

session_archive:
	# Prepare an archive containing all session files of the testsuite.
	# This is useful for the "replay" mailserver to recreate sessions.
	find testsuite/gnatprove -name why3session.xml > sessions.txt
	tar -czf sessions.tgz -T sessions.txt
	rm sessions.txt

gnatprove:
	$(MAKE) -f Makefile.gnatprove build

gnatprove-nightly:
	$(MAKE) -f Makefile.gnatprove build PROD=$(PROD)

install-examples:
	mkdir -p $(EXAMPLESDIR)
	# install examples from the testsuite as identified in file
	# MANIFEST.examples
	for dir in `grep -v "^--" MANIFEST.examples` ; do \
	   $(CP) testsuite/gnatprove/tests/$$dir $(EXAMPLESDIR); \
	done
	find $(EXAMPLESDIR) -name test.py -exec rm -f {} \;
	find $(EXAMPLESDIR) -name test.out -exec rm -f {} \;
	# install examples in SPARK User's Guide
	mkdir $(EXAMPLESDIR)/gnatprove_by_example
	$(CP) testsuite/gnatprove/tests/ug__* \
	  $(EXAMPLESDIR)/gnatprove_by_example
	$(CP) docs/ug/gnatprove_by_example.gpr docs/ug/test.adc \
	  $(EXAMPLESDIR)/gnatprove_by_example
clean:
	$(MAKE) -C gnat2why clean
	$(MAKE) -f Makefile.gnatprove clean
	$(MAKE) -C docs/ug clean
	$(MAKE) -C docs/lrm clean
	$(MAKE) -C why3 clean
	$(MAKE) -C include clean
	rm -f docs/sphinx_support/confvars.py

BENCHDIR=bench
RESULTSDIR=benchout
create-benchmark:
	rm -rf $(BENCHDIR)
	mkdir -p $(BENCHDIR)
	testsuite/gnatprove/bench/create_benchmarks.py --testsuite-dir=testsuite/gnatprove --target-dir=$(BENCHDIR) --testlist=testsuite/gnatprove/MANIFEST.bench

run-benchmark:
	testsuite/gnatprove/bench/benchtests.py -j0 --testsuite-dir=testsuite/gnatprove $(BENCHDIR) --results-dir=$(RESULTSDIR)
	testsuite/gnatprove/bench/gaia.py --testsuite-dir=testsuite/gnatprove $(RESULTSDIR)/results.json

format:
	gnatformat -P gnatprove --no-subprojects
	gnatformat -P gnat2why/gnat2why.gpr --no-subprojects

check-format:
	gnatformat -P gnatprove --check --no-subprojects
	gnatformat -P gnat2why/gnat2why.gpr --check --no-subprojects
