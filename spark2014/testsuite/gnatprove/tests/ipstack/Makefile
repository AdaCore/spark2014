# Settings for powerpc-elf target

RTS=zfp
GCC_PREFIX=powerpc-elf-
GNATPRJ_FLAGS=-XVARIANT="$(ZFP_VARIANT)"
ZFP_VARIANT=powerpc-elf-qemu

# Settings for native target
#RTS=native
#GCC_PREFIX=
#GNATPRJ_FLAGS=

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
	cd $(dir $(LWIPLIB)) && make clean GCC_PREFIX="$(GCC_PREFIX)"
	$(GCC_PREFIX)gnatclean $(GNATPRJ_FLAGS) -q -r -P projects/ipstack
	rm -f projects/ipstack_support.gpr

$(APP_IMAGE).bin: $(APP_IMAGE)
	powerpc-elf-objcopy -O binary $< $@

run: $(APP_IMAGE).bin
	qemu-system-ppc -nographic -M prep -L $(dir $<) -bios $(notdir $<) -net nic -net tap,script=scripts/qemu-ifup
	
# LWIP

$(LWIPLIB): force
	cd $(LWIPDIR) && make liblwip4.a GCC_PREFIX="$(GCC_PREFIX)"

force:
