sparkify -w -q *.ads *.adb
if [ $? -ne 0 ]; then
  echo "Sparkify terminates in error"
  exit
fi
cd sparkified
echo "------------------------------------------------------------------------"
cat *.ads *.adb
echo "------------------------------------------------------------------------"
sparkmake > dummy.log
# start diff wrt common test driver, cf J618-015
cp ../spark.smf .
# end diff wrt common test driver
spark -noecho -fdl=_fdl_ -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
if [ $? -ge 2 ]; then
  echo "Examiner terminates in error"
  exit
fi
sparksimp > dummy.log
pogs > dummy.log
tail -11 *.sum
