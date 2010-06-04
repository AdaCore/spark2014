sparkify -w -q *.ads *.adb
cd sparkified
echo "------------------------------------------------------------------------"
cat *.ads *.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
if [ $? -ge 2 ]; then
  exit
fi
sparksimp > dummy.log
pogs > dummy.log
tail -11 *.sum
