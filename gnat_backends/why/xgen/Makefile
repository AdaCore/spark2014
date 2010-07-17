
all: why-ids.ads

why-sinfo.adt:
	gcc -c -gnatct ../why-sinfo.ads

why-ids.ads: xkinds why-sinfo.adt why-ids.ads-head why-ids.ads-tail
	cat why-ids.ads-head >  why-ids.ads
	./xkinds             >> why-ids.ads
	cat why-ids.ads-tail >> why-ids.ads

xkinds: xkinds.adb
	gnatmake -Phelpers

clean:
	-rm *~
	-rm *.o
	-rm *.ali
	-rm b~* 
	-rm *.adt
	-rm why-ids.ads
	-rm xkinds
