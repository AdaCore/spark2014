pragma SPARK_Mode;
with System;
procedure Q (A : System.Address) is
   Y : Integer with Address => A;
begin
   null;
end Q;
