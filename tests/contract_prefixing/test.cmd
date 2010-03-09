sparkify -w -q s.ads s.adb t.ads
cd sparkified
echo "------------------------------------------------------------------------"
cat s.ads s.adb t.ads
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp >> dummy.log
pogs -o=s.sum >> dummy.log
tail -11 s.sum
