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
spark -noecho -flow=data -config=$TEST_SUPPORT/standard.ads -vcg @spark
if [ $? -ge 2 ]; then
  echo "Examiner terminates in error"
  exit
fi

# Special rules added
cp ../internal_asm_stack.rlu internal_asm_stack

sparksimp > dummy.log
pogs > dummy.log
tail -11 *.sum
