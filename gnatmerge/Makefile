INSTALLDIR=install
CP=cp -pr
MKDIR=mkdir -p

DUMMY:=$(shell $(MKDIR) bin)

all: build

build: force
	make -C ada build

force:

clean:
	make -C ada clean

install: build
	mkdir -p $(INSTALLDIR)/share/
	mkdir -p $(INSTALLDIR)/bin/
	$(CP) share/gnatmerge/ $(INSTALLDIR)/share/
	$(CP) bin/gnatmerge $(INSTALLDIR)/bin/
