sparkify -w -q tq.ads tq.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat tq.ads tq.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp > dummy.log
pogs -o=tq.sum > dummy.log
tail -11 tq.sum
