sparkify -w -q cursor_location.ads cursor_location.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat cursor_location.ads cursor_location.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
sparksimp > dummy.log
pogs -o=cursor_location.sum > dummy.log
tail -11 cursor_location.sum
