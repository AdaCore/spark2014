package body Read_Write with
  SPARK_Mode
is

   procedure Q is
   begin
      V := True;
   end Q;

   procedure P is
   begin
      V := False;  --  Flow warning that never gets emitted
      V := True;
   end P;

end Read_Write;
