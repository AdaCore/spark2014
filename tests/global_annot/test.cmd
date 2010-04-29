sparkify -w -q globals.ads globals.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat globals.ads globals.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark \
| grep "errors or warnings"
echo "------------------------------------------------------------------------"
sparksimp > dummy.log
pogs -o=globals.sum > dummy.log
tail -11 globals.sum
