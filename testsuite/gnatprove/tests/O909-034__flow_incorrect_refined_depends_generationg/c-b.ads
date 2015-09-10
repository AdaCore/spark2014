with System;

private package C.B
with
   SPARK_Mode
is

   X : Integer
   with
      Volatile,
      Part_Of => C.State;

   Y : Integer
   with
      Part_Of => C.State;

end C.B;