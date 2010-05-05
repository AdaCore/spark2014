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

.PHONY: app ipstack clean force sparkmake spark

LWIPDIR=src/lwip4aip
LWIPLIB=$(LWIPDIR)/liblwip4.a

APP=echop
APP_IMAGE=build/app/$(APP)

app: $(APP_IMAGE)

$(APP_IMAGE): $(LWIPLIB) ipstack force
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P app

ipstack: force
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_core
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_support
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_services

clean:
	cd $(dir $(LWIPLIB)) && make clean TARGET="$(TARGET)"
	$(GCC_PREFIX)gnatclean $(GNATPRJ_FLAGS) -q -r -P ipstack
	rm -fr spark

$(APP_IMAGE).bin: $(APP_IMAGE)
	powerpc-elf-objcopy -O binary $< $@

run: $(APP_IMAGE).bin
	qemu-system-ppc -nographic -M prep -L $(dir $<) -bios $(notdir $<) -net nic -net tap,script=scripts/qemu-ifup
	
# LWIP

$(LWIPLIB): force
	cd $(LWIPDIR) && make liblwip4.a TARGET="$(TARGET)"

spark/spark.idx:
	mkdir -p spark
	cd spark && sparkmake -directory=../src/core/ -directory=../src/lwip4aip/ -directory=../src/services/ -directory=../src/support/ -directory=../src/support.$(TARGET)/

spark: spark/spark.idx
	cd spark && spark -flow=data @spark

force:
