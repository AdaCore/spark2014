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

uname:=$(shell uname)

ifeq ($(filter-out CYGWIN%,$(uname)),)
  LDFLAGS=-Wl,--stack=0x2000000
  LN_S=cp -p
else
  LN_S=ln -sf
endif

.PHONY: setup force clean

all: build

setup:
	mkdir -p obj obj-tools ../install/bin
	sed -e "s^@ADAINCLUDE@^$(adainclude)^" \
	    -e "s^@ADALIB@^$(adalib)^" \
	    -e "s^@PREFIX@^$(prefix)^" \
	    -e "s^@GNAT1DIR@^$(gnat1dir)^" \
	    sdefault.adb.in > obj/sdefault.adb
	for f in `cd gnat_src; ls xtreeprs.adb xnmake.adb xutil.ad? *-tmpl sinfo.ads treeprs.adt nmake.adt`; \
	do \
	  cp -p gnat_src/$$f obj-tools; \
	done
	cd obj-tools && gnatmake -q xtreeprs xnmake &&\
	./xtreeprs && ./xnmake && mv nmake.ads nmake.adb treeprs.ads ../obj
	cd obj && $(LN_S) ../gnat_src/*.ad[sb] . && \
	$(RM) x*.ad? ?-*.ad? mlib* back_end.adb system.ads ada.ads \
	  gnat.ads interfac.ads `cat ../gnat_src/MANIFEST.gnat_util` && \
	mv -f ada_get_targ.adb get_targ.adb

build: setup force
	$(GPRBUILD) $(GPRARGS) -Pgnat2why -j$(PROCS) -largs $(LDFLAGS)

coverage: setup force
	$(GPRBUILD) $(GPRARGS) -Pgnat2why -j$(PROCS) \
	  -cargs -fprofile-arcs -ftest-coverage \
	  -largs $(LDFLAGS) -fprofile-arcs -ftest-coverage

force:

clean:
	-$(RM) obj obj-tools
