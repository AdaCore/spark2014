
GENERATED_FILES= \
 why-atree-accessors.ads      \
 why-atree-builders.ads       \
 why-atree-builders.adb       \
 why-atree-mutators.ads       \
 why-atree-mutators.adb       \
 why-atree-traversal.ads      \
 why-atree-traversal.adb      \
 why-atree-traversal_stub.ads \
 why-atree-traversal_stub.adb \
 why-atree-validity.ads       \
 why-ids.ads                  \
 why-kind_validity.ads        \
 why-opaque_ids.ads           \
 why-unchecked_ids.ads

ASIS_FILES=\
 why-sinfo.adt \
 why-atree.adt

all: $(GENERATED_FILES)

force:

why-sinfo.adt: ../why-sinfo.ads
	gcc -c -gnatct ../why-sinfo.ads

why-atree.adt: ../why-atree.ads
	gcc -c -gnatct ../why-atree.ads -I../../gnat_src

why-atree-accessors.ads: xtree $(ASIS_FILES) why-atree-accessors.ads-tmpl
	./xtree

why-atree-mutators.ads: xtree $(ASIS_FILES) why-atree-mutators.ads-tmpl
	./xtree

why-atree-mutators.adb: xtree $(ASIS_FILES) why-atree-mutators.adb-tmpl
	./xtree

why-atree-builders.ads: xtree $(ASIS_FILES) why-atree-builders.ads-tmpl
	./xtree

why-atree-builders.adb: xtree $(ASIS_FILES) why-atree-builders.adb-tmpl
	./xtree

why-atree-traversal.ads: xtree $(ASIS_FILES) why-atree-traversal.ads-tmpl
	./xtree

why-atree-traversal.adb: xtree $(ASIS_FILES) why-atree-traversal.adb-tmpl
	./xtree

why-atree-traversal_stub.ads: xtree $(ASIS_FILES) why-atree-traversal_stub.ads-tmpl
	./xtree

why-atree-traversal_stub.adb: xtree $(ASIS_FILES) why-atree-traversal_stub.adb-tmpl
	./xtree

why-atree-validity.ads: xtree $(ASIS_FILES) why-atree-validity.ads-tmpl
	./xtree

why-ids.ads: xtree why-sinfo.adt why-ids.ads-tmpl
	./xtree

why-kind_validity.ads: xtree why-sinfo.adt why-kind_validity.ads-tmpl
	./xtree

why-opaque_ids.ads: xtree why-sinfo.adt why-opaque_ids.ads-tmpl
	./xtree

why-unchecked_ids.ads: xtree why-sinfo.adt why-unchecked_ids.ads-tmpl
	./xtree

xtree: force
	gnatmake -Phelpers xtree

clean:
	-rm *~
	-rm *.o
	-rm *.ali
	-rm b~* 
	-rm *.adt
	-rm xtree
