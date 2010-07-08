ifeq ($(TARGET),native)
GCC_PREFIX=
GNATPRJ_FLAGS=

else ifeq ($(TARGET),powerpc-elf)
RTSFLAG=--RTS=zfp
GCC_PREFIX=$(TARGET)-
GNATPRJ_FLAGS=-XVARIANT="$(ZFP_VARIANT)"
ZFP_VARIANT=powerpc-elf-qemu

else
$(error Please define TARGET)
endif

# Settings for native target

# Common settings

GNATPRJ_FLAGS+=-aPprojects:projects.$(TARGET)
GNATMAKE_FLAGS=-g -j4 $(RTSFLAG) $(GNATPRJ_FLAGS)
GNATCLEAN_FLAGS=$(GNATPRJ_FLAGS)

BUILDER=$(GCC_PREFIX)gnatmake
#BUILDER=gprbuild $(if $(filter $(TARGET), native),,--target=$(TARGET))
# gprbuild disabled for now as it seems to fail to notice modified files

.PHONY: app ipstack clean force spark

LWIPDIR=src/lwip4aip
LWIPLIB=$(LWIPDIR)/liblwip4.a

APP=echop
APP_IMAGE=build/app/$(APP)

app: $(APP_IMAGE)

$(APP_IMAGE): $(LWIPLIB) ipstack force
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P app

ipstack: build/gen/aip_constants.ads \
         $(foreach proto,            \
           arp ip icmp udp tcp,      \
           build/gen/aip-$(proto)h.ads build/gen/aip-$(proto)h.adb)
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_core
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_support
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_services

build/bldtools/tranxgen: src/bldtools/tranxgen.adb
	mkdir -p build/bldtools
	gnatmake -g -D build/bldtools -o $@ $< `xmlada-config`

build/gen/aip-%.ads build/gen/aip-%.adb: src/proto/%.xml build/bldtools/tranxgen
	mkdir -p build/gen
	adaf=build/gen/$(notdir $<).ada; \
	build/bldtools/tranxgen $< > $$adaf; \
	gnatchop -w $$adaf build/gen

build/gen/aip_constants.ads:
	mkdir -p build/gen
	$(GCC_PREFIX)gcc -S -o build/gen/constants.s src/bldtools/constants.adb
	(echo "package AIP_Constants is"; \
	echo "   pragma Pure;";\
	sed -n '/->CND:[^:]*:\([^:]*\):[^0-9]*\([0-9]*\):.*/s//   \1 : constant := \2;/p' < build/gen/constants.s ;\
	echo "end AIP_Constants;") > build/gen/aip_constants.ads

clean:
	cd $(dir $(LWIPLIB)) && make clean TARGET="$(TARGET)"
	$(GCC_PREFIX)gnatclean $(GNATPRJ_FLAGS) -q -r -P ipstack
	rm -fr spark build

$(APP_IMAGE).bin: $(APP_IMAGE)
	powerpc-elf-objcopy -O binary $< $@

run: $(APP_IMAGE).bin
	qemu-system-ppc -nographic -M prep -L $(dir $<) -bios $(notdir $<) -net nic -net tap,script=scripts/qemu-ifup
	
# LWIP

$(LWIPLIB): force
	cd $(LWIPDIR) && make liblwip4.a TARGET="$(TARGET)"

spark/spark.idx:
	mkdir -p spark
	cd spark && sparkmake -directory=../build/gen -directory=../src/core/ -directory=../src/lwip4aip/ -directory=../src/services/ -directory=../src/support/ -directory=../src/support.$(TARGET)/

spark: spark/spark.idx
	cd spark && spark -flow=data @spark

force:
