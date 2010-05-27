sparkify -w -q discrete_range.ads discrete_range.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat discrete_range.ads discrete_range.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp > dummy.log
pogs -o=discrete_range.sum > dummy.log
tail -11 discrete_range.sum
