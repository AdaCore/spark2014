sparkify -w -q s.ads s.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat s.ads s.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp >> dummy.log
pogs -o=s.sum >> dummy.log
tail -11 s.sum
