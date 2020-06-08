# Generic part of the backend Makefile.
# This makefile assumes that it executed from the backend directory.

GPRBUILD=gprbuild
PROJECTFILE=gnat2why

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
	mkdir -p obj obj-tools ../install/bin
	sed -e "s^@ADAINCLUDE@^$(adainclude)^" \
	    -e "s^@ADALIB@^$(adalib)^" \
	    -e "s^@PREFIX@^$(prefix)^" \
	    -e "s^@GNAT1DIR@^$(gnat1dir)^" \
	    sdefault.adb.in > obj/sdefault.adb
	for f in `cd gnat_src; ls xtreeprs.adb xnmake.adb xutil.ad? *-tmpl sinfo.ads treeprs.adt nmake.adt xsnamest.adb`; \
	do \
	  cp -p gnat_src/$$f obj-tools; \
	done
	cd obj-tools && $(GPRBUILD) -q xtreeprs xnmake xsnamest && \
	./xtreeprs && ./xnmake && mv nmake.ads nmake.adb treeprs.ads ../obj && \
	./xsnamest && mv snames.ns ../obj/snames.ads && mv snames.nb ../obj/snames.adb
	cp -f gnat_src/ada_get_targ.adb obj/get_targ.adb

build: setup force
	$(GPRBUILD) $(GPRARGS) -P$(PROJECTFILE) -j$(PROCS) -cargs ${CFLAGS} -largs $(LDFLAGS)

# Compilation and linking settings for coverage and profiling; for details see
# "Code Coverage and Profiling" in GNAT User's Guide.

coverage-setup: force
	gnatcov instrument -P gnat2why.gpr --level=stmt --dump-trigger=atexit
	# ??? insert newlines into the gnatcov output; otherwise we would have
	# too long lines
	sed -i 's/;[^ ]/\n&/g' obj/gnatcov-instr/gnat1drv.adb
	mkdir -p obj_coverage

coverage: GPRARGS=-XBuild=Coverage --src-subdirs=gnatcov-instr
coverage: PROJECTFILE=gnat2why_coverage
coverage: coverage-setup build

profile: CFLAGS = -pg
profile: LDFLAGS += -pg
profile: build

codepeer-run: setup force
	codepeer -P gnat2why.gpr

codepeer:
	@codepeer -P gnat2why.gpr -quiet -output-msg-only

force:

clean:
	$(MAKE) -C ../src/why/xgen clean
	-$(RM) obj obj-tools
