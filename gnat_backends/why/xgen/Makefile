
all: why-ids.ads why-atree-builders.ads

why-sinfo.adt: ../why-sinfo.ads
	gcc -c -gnatct ../why-sinfo.ads

why-atree.adt: ../why-atree.ads
	gcc -c -gnatct ../why-atree.ads -I../../gnat_src

why-ids.ads: xkinds why-sinfo.adt why-ids.ads-head why-ids.ads-tail
	cat why-ids.ads-head >  why-ids.ads
	./xkinds             >> why-ids.ads
	cat why-ids.ads-tail >> why-ids.ads

why-atree-builders.ads: xtree why-atree.adt why-atree-builders.ads-head why-atree-builders.ads-tail
	cat why-atree-builders.ads-head >  why-atree-builders.ads
	./xtree                         >> why-atree-builders.ads
	cat why-atree-builders.ads-tail >> why-atree-builders.ads

xkinds: xkinds.adb
	gnatmake -Phelpers xkinds

xtree: xtree.adb
	gnatmake -Phelpers xtree

clean:
	-rm *~
	-rm *.o
	-rm *.ali
	-rm b~* 
	-rm *.adt
	-rm why-ids.ads
	-rm why-atree-builders.ads
	-rm xkinds
	-rm xtree
