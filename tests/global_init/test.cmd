sparkify -w -q globals.ads globals.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat globals.ads globals.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp > dummy.log
pogs -o=globals.sum > dummy.log
tail -11 globals.sum
