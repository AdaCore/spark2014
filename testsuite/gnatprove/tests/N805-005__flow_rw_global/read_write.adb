package body Read_Write
is

   V : Boolean;

   procedure Test_01 with
     Global => (In_Out => V),
     Pre    => not V
   is
   begin
      V := True;
   end Test_01;

   --  Should produce an error
   procedure Test_02 with
     Global => (In_Out => V),
     Post   => V
   is
   begin
      V := True;
   end Test_02;

   procedure Test_03 with
     Global => (In_Out => V)
   is
   begin
      pragma Assert (not V);
      V := True;
   end Test_03;

   procedure Wibble
   is
   begin
      pragma Assert (not V);
      V := True;
   end Wibble;

   procedure Test_04 with
     Global => (In_Out => V)
   is
   begin
      Wibble;
   end Test_04;

end Read_Write;
