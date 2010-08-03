
all: why-ids.ads why-atree-builders.ads

force:

why-sinfo.adt: ../why-sinfo.ads
	gcc -c -gnatct ../why-sinfo.ads

why-atree.adt: ../why-atree.ads
	gcc -c -gnatct ../why-atree.ads -I../../gnat_src

why-ids.ads: xkinds why-sinfo.adt why-ids.ads-tmpl why-unchecked_ids.ads-tmpl
	./xkinds

why-atree-builders.ads: xtree why-atree.adt why-atree-builders.ads-tmpl
	./xtree

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
