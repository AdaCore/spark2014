.PHONY: test

test:
	gnatmake test
	./test

spark:
	spark -vcg -brief -i=spark.idx @spark.smf
	sparksimp -p=4
	pogs
