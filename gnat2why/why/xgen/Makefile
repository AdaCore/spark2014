.PHONY: all

GENERATED_FILES= \
 why-classes.ads              \
 why-atree.ads                \
 why-atree-accessors.ads      \
 why-atree-builders.ads       \
 why-atree-builders.adb       \
 why-atree-mutators.ads       \
 why-atree-mutators.adb       \
 why-atree-traversal.ads      \
 why-atree-traversal.adb      \
 why-atree-traversal_stub.ads \
 why-atree-traversal_stub.adb \
 why-atree-treepr.ads         \
 why-atree-treepr.adb         \
 why-atree-validity.ads       \
 why-conversions.ads          \
 why-ids.ads                  \
 why-kind_validity.ads        \
 why-opaque_ids.ads           \
 why-unchecked_ids.ads

all:
	gprbuild -j0 -p -Phelpers xtree
	./xtree
	cp $(GENERATED_FILES) ../

clean:
	-rm -f *~
	-rm -f *.o
	-rm -f *.ali
	-rm -f b~*
	-rm -f xtree
	-rm -f $(GENERATED_FILES)
