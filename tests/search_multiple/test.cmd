sparkify -w -q search.ads search.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat search.ads search.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp > dummy.log
pogs -o=search.sum > dummy.log
tail -11 search.sum
