
GENERATED_FILES= \
 why-atree-accessors.ads \
 why-atree-builders.ads  \
 why-atree-builders.adb  \
 why-atree-traversal.ads \
 why-atree-traversal.adb \
 why-ids.ads             \
 why-unchecked_ids.ads

all: $(GENERATED_FILES)

force:

why-sinfo.adt: ../why-sinfo.ads
	gcc -c -gnatct ../why-sinfo.ads

why-atree.adt: ../why-atree.ads
	gcc -c -gnatct ../why-atree.ads -I../../gnat_src

why-atree-accessors.ads: xtree why-atree.adt why-atree-accessors.ads-tmpl
	./xtree

why-atree-builders.ads: xtree why-atree.adt why-atree-builders.ads-tmpl
	./xtree

why-atree-builders.adb: xtree why-atree.adt why-atree-builders.adb-tmpl
	./xtree

why-atree-traversal.ads: xtree why-atree.adt why-atree-traversal.ads-tmpl
	./xtree

why-atree-traversal.adb: xtree why-atree.adt why-atree-traversal.adb-tmpl
	./xtree

why-ids.ads: xkinds why-sinfo.adt why-ids.ads-tmpl
	./xkinds

why-unchecked_ids.ads: xkinds why-sinfo.adt why-unchecked_ids.ads-tmpl
	./xkinds

xkinds: force
	gnatmake -Phelpers xkinds

xtree: force
	gnatmake -Phelpers xtree

clean:
	-rm *~
	-rm *.o
	-rm *.ali
	-rm b~* 
	-rm *.adt
	-rm xkinds
	-rm xtree
