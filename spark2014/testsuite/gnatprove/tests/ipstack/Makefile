#TARGET=native
TARGET=powerpc-elf

ifeq ($(TARGET),native)
RTS=native
GCC_PREFIX=
GNATPRJ_FLAGS=

else
# powerpc-elf
RTS=zfp
GCC_PREFIX=$(TARGET)-
GNATPRJ_FLAGS=-XVARIANT="$(ZFP_VARIANT)"
ZFP_VARIANT=powerpc-elf-qemu
endif

# Settings for native target

# Common settings

GNATMAKE_FLAGS=--RTS=$(RTS) $(GNATPRJ_FLAGS)
GNATCLEAN_FLAGS=$(GNATPRJ_FLAGS)

.PHONY: app ipstack clean force

LWIPDIR=src/lwip4aip
LWIPLIB=$(LWIPDIR)/liblwip4.a

APP=echop
APP_IMAGE=build/app/$(APP)

app: $(APP_IMAGE)

$(APP_IMAGE): $(LWIPLIB) ipstack force
	$(GCC_PREFIX)gnatmake $(GNATMAKE_FLAGS) -p -P projects/app

ipstack: force
	$(GCC_PREFIX)gnatmake $(GNATMAKE_FLAGS) -p -P projects/ipstack_core
	$(GCC_PREFIX)gnatmake $(GNATMAKE_FLAGS) -p -P projects/ipstack_support
	$(GCC_PREFIX)gnatmake $(GNATMAKE_FLAGS) -p -P projects/ipstack_services

clean:
	cd $(dir $(LWIPLIB)) && make clean TARGET="$(TARGET)"
	$(GCC_PREFIX)gnatclean $(GNATPRJ_FLAGS) -q -r -P projects/ipstack

$(APP_IMAGE).bin: $(APP_IMAGE)
	powerpc-elf-objcopy -O binary $< $@

run: $(APP_IMAGE).bin
	qemu-system-ppc -nographic -M prep -L $(dir $<) -bios $(notdir $<) -net nic -net tap,script=scripts/qemu-ifup
	
# LWIP

$(LWIPLIB): force
	cd $(LWIPDIR) && make liblwip4.a TARGET="$(TARGET)"

force:
