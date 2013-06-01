
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

all: $(GENERATED_FILES)
	cp $(GENERATED_FILES) ../

force:

why-atree.ads: xtree why-atree.ads-tmpl
	./xtree

why-atree-accessors.ads: xtree why-atree-accessors.ads-tmpl
	./xtree

why-atree-mutators.ads: xtree why-atree-mutators.ads-tmpl
	./xtree

why-atree-mutators.adb: xtree why-atree-mutators.adb-tmpl
	./xtree

why-atree-builders.ads: xtree why-atree-builders.ads-tmpl
	./xtree

why-atree-builders.adb: xtree why-atree-builders.adb-tmpl
	./xtree

why-atree-traversal.ads: xtree why-atree-traversal.ads-tmpl
	./xtree

why-atree-traversal.adb: xtree why-atree-traversal.adb-tmpl
	./xtree

why-atree-traversal_stub.ads: xtree why-atree-traversal_stub.ads-tmpl
	./xtree

why-atree-traversal_stub.adb: xtree why-atree-traversal_stub.adb-tmpl
	./xtree

why-atree-treepr.ads: xtree why-atree-treepr.ads-tmpl
	./xtree

why-atree-treepr.adb: xtree why-atree-treepr.adb-tmpl
	./xtree

why-atree-validity.ads: xtree why-atree-validity.ads-tmpl
	./xtree

why-ids.ads: xtree why-ids.ads-tmpl
	./xtree

why-kind_validity.ads: xtree why-kind_validity.ads-tmpl
	./xtree

why-opaque_ids.ads: xtree why-opaque_ids.ads-tmpl
	./xtree

why-classes.ads: xtree why-classes.ads-tmpl
	./xtree

why-unchecked_ids.ads: xtree why-unchecked_ids.ads-tmpl
	./xtree

xtree: force
	gnatmake -j0 -Phelpers xtree

clean:
	-rm -f *~
	-rm -f *.o
	-rm -f *.ali
	-rm -f b~*
	-rm -f xtree
