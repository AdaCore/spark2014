package body My_Type_Invariant_Test_Init
  with SPARK_Mode => On
is
   procedure Test is
   begin
      pragma Assert (Bar.My_Field = True);
      pragma Assert (Bad.My_Field = True);
   end Test;

begin
   Bar.My_Field := False;
end My_Type_Invariant_Test_Init;
