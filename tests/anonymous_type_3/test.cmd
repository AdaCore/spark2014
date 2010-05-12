sparkify -w -q anon_type.ads anon_type.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat anon_type.ads anon_type.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp > dummy.log
pogs -o=anon_type.sum > dummy.log
tail -11 anon_type.sum
