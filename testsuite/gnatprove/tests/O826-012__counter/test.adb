package body Test
   with SPARK_Mode
is

 procedure P
 (X : in integer;
 Y : out integer)
 with
 SPARK_Mode is
 begin
  Y:= 4*X*X*X*X + 4;
 end P;
end Test;
