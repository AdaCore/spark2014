package body Test
is

   procedure Loc (X1, X2 : out Integer) is
   begin
      X1 := 0;
      X2 := 0;
   end Loc;

   procedure Test_01 (B : Boolean; Z : in out Integer) is
      Y : Integer;
   begin
      if B then
         Loc (Y, Z);
      end if;
      Y := 0;
      Z := Z + Y;
   end Test_01;

   procedure Test_02 (B : Boolean; Z : in out Integer) is
      Y : Integer;
   begin
      if B then
         Loc (Y, Z);
      end if;
   end Test_02;

end Test;
