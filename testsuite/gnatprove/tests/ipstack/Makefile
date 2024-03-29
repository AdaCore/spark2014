ifeq ($(TARGET),native)
GCC_PREFIX=
GNATPRJ_FLAGS=

else

ifeq ($(TARGET),powerpc-elf)
RTSFLAG=--RTS=zfp-prep
GCC_PREFIX=$(TARGET)-
ZFP_VARIANT=powerpc-elf-qemu

else
$(error Please define TARGET)
endif
endif

# Settings for native target

# Common settings

PROCESSORS=4
GNATPRJ_FLAGS+=-aPprojects:projects.$(TARGET)
GNATMAKE_FLAGS=-j$(PROCESSORS) $(RTSFLAG) $(GNATPRJ_FLAGS)
GNATCLEAN_FLAGS=$(GNATPRJ_FLAGS)

#BUILDER=$(GCC_PREFIX)gnatmake
BUILDER=gprbuild $(if $(filter $(TARGET), native),,--target=$(TARGET))
# gprbuild disabled for now as it seems to fail to notice modified files

.PHONY: app ipstack clean force spark

APP=echop
APP_IMAGE=build/app/$(APP)

app: $(APP_IMAGE)

$(APP_IMAGE): ipstack force
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P app

test: ipstack force
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P test

build-test: force
	@$(BUILDER) $(GNATMAKE_FLAGS) -q -p -P $(TEST_GPR)

ipstack: build/gen/aip_constants.ads  \
         $(foreach proto,             \
           ether arp ip icmp udp tcp, \
           build/gen/aip-$(proto)h.ads build/gen/aip-$(proto)h.adb)
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_core
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_support
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_services
	$(BUILDER) $(GNATMAKE_FLAGS) -p -P ipstack_dev

build/bldtools/tranxgen: src/bldtools/tranxgen.adb
	mkdir -p build/bldtools
	gprbuild -g tranxgen.gpr

build/gen/aip-%.ads build/gen/aip-%.adb: src/proto/%.xml build/bldtools/tranxgen
	mkdir -p build/gen
	adaf=build/gen/$(subst .xml,.ada,$(notdir $<)) && \
	build/bldtools/tranxgen -o build/gen -x AIP_ $< && \
	gnatchop -w $$adaf build/gen

build/gen/aip_constants.ads: src/bldtools/constants.adb
	mkdir -p build/gen
	$(BUILDER) $(GNATMAKE_FLAGS) -f -c -p -P ipstack_constants
	( \
	echo "--  Automatically generated by "`gnatmake --version | head -1`; \
	echo "--  for "`$(GCC_PREFIX)gcc -dumpmachine`; \
	echo "--  DO NOT EDIT!!!"; \
	echo ""; \
	echo "package AIP_Constants is"; \
	echo "   pragma Pure;";\
	sed -n '/->CND:[^:]*:\([^:]*\):[^0-9]*\([0-9]*\):.*/s//   \1 : constant := \2;/p' < build/gen/constants.s ;\
	echo "end AIP_Constants;") > build/gen/aip_constants.ads

clean:
	gnatclean $(GNATPRJ_FLAGS) -q -r -P ipstack
	rm -fr spark build

$(APP_IMAGE).bin: $(APP_IMAGE)
	$(GCC_PREFIX)objcopy -O binary $< $@

run: $(APP_IMAGE).bin
	qemu-system-ppc -nographic -s -M prep -L $(dir $<) -bios $(notdir $<) -net nic -net tap,script=testsuite/qemu/qemu-ifup

# Currently apply only flow analysis.
spark: force
	mkdir -p spark && \
	cd spark && \
	gnatprove -aP ../projects -aP ../projects.native -P../projects.native/ipstack_dev.gpr --mode=flow --warnings=continue --output=brief --quiet 2>&1 | sort

codepeer: force
	$(MAKE) TARGET=$(TARGET) \
	   GNATMAKE_FLAGS="$(GNATMAKE_FLAGS) -c --subdirs=codepeer -gnatcC" \
	   ipstack
	codepeer -all -lib ipstack.lib -global -background -quiet
	@echo ""
	@echo "codepeer completed successfully."
	@echo "to view messages, run: codepeer_msg_reader build/ipstack.output"
	@echo "or: firefox build/ipstack.output/html/index.html"

force:
