# Generic part of the backend Makefile.
# This makefile assumes that it executed from the backend directory.

GPRBUILD=gprbuild

# number of processors
PROCS=0

# Set to 1 to enable automated (as opposed to manual) builds
AUTOMATED=0

RM=rm -rf
MV=mv -f
# adainclude and adalib are later used as input for sed, so we replace
# backward slashes by forward slashes to avoid sed interpreting those
adainclude:=$(subst \,/,$(strip $(shell gnatls -v | grep adainclude)))
adalib:=$(subst \,/,$(strip $(shell gnatls -v | grep adalib)))
gnat1dir:=$(shell echo $(adainclude) | sed -e 's^rts-.*^^' -e 's^adainclude^^')

ifeq ($(AUTOMATED),1)
  GPRARGS=-XBuild=Production
  prefix=$(shell echo $(adainclude) | sed -e 's!\(.*\)/lib/gcc/\(.*\)!\1!')/
else
  prefix:=@NOPREFIX@
endif

# symbolic linking of GNAT files is fast and that's how CodePeer is built too
USE_LN=true
uname:=$(shell uname)

ifeq ($(filter-out CYGWIN%,$(uname)),)
  LDFLAGS=-Wl,--stack=0x2000000
  USE_LN=false
endif

GEN_IL_FILES = nmake.adb nmake.ads \
  seinfo.ads sinfo-nodes.ads sinfo-nodes.adb \
  einfo-entities.ads einfo-entities.adb

.PHONY: setup force clean

all: build

setup_precheck:
	@if [ ! -d gnat_src ]; \
	then \
	  echo "error: missing directory or link \"gnat_src\" to GNAT sources"; \
	  false; \
	fi

setup: setup_precheck
	$(MAKE) -C ../src/why/xgen
	mkdir -p obj obj-gnat obj-gnat2why obj-tools ../install/bin
	sed -e "s^@ADAINCLUDE@^$(adainclude)^" \
	    -e "s^@ADALIB@^$(adalib)^" \
	    -e "s^@PREFIX@^$(prefix)^" \
	    -e "s^@GNAT1DIR@^$(gnat1dir)^" \
	    sdefault.adb.in > obj/sdefault.adb
	cp -f gnat_src/ada_get_targ.adb obj/get_targ.adb
	for f in gnat1drv.adb ;\
	do \
	  cp -pf gnat_src/$$f obj-gnat2why; \
	done
	cp -pf gnat_src/libgnat/s-rident.ads obj-gnat
	for f in `cd gnat_src; ls gen_il*.ad? xutil.ad? *-tmpl xsnamest.adb`; \
	do \
	  cp -p gnat_src/$$f obj-tools; \
	done
	cd obj-tools && $(GPRBUILD) -q xsnamest && ./xsnamest && \
	mv snames.ns ../obj/snames.ads && mv snames.nb ../obj/snames.adb && \
	$(GPRBUILD) -q -j0 gen_il-main.adb -cargs -I../obj && ./gen_il-main && \
	mv $(GEN_IL_FILES) ../obj

build: setup force
	$(GPRBUILD) $(GPRARGS) $(COVERAGEARGS) -Pgnat2why -j$(PROCS) -cargs ${CFLAGS} -largs $(LDFLAGS)

# Compilation and linking settings for coverage and profiling; for details see
# "Code Coverage and Profiling" in GNAT User's Guide.
#
# Note: "gnatcov instrument" requires a full compilable closure, so
# this target depends on "setup", which generates some required
# source files.

coverage-setup: setup force
	gnatcov instrument --no-subprojects -P gnat2why.gpr --level=stmt --dump-trigger=atexit
	mkdir -p obj_coverage

coverage: COVERAGEARGS=-XCoverage=yes --src-subdirs=gnatcov-instr --implicit-with=gnatcov_rts
coverage: coverage-setup build

profile: CFLAGS = -pg
profile: LDFLAGS += -pg
profile: build

codepeer-run: setup force
	gnatsas analyze -P gnat2why.gpr --no-gnat

codepeer:
	@gnatsas report text -P gnat2why.gpr --quiet
	@gnatsas report code-climate -P gnat2why.gpr --quiet -o obj/gnatsas/gnat2why.json

force:

clean:
	$(MAKE) -C ../src/why/xgen clean
	-$(RM) obj obj-tools obj-gnat obj-gnat2why
