package Ghostarr with SPARK_Mode is
   task type XX;
   type YY is array (1 .. 3) of XX;
   type ZZ is array (1 .. 3) of YY with Ghost;
end;
