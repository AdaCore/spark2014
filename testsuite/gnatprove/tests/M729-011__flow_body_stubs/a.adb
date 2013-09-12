package body A
is
   

   procedure Swap_A (X, Y : in out Integer)
   is
      Tmp : Integer;
   begin
      Tmp := X;
      X := Y;
      Y := Tmp;
   end Swap_A;

   procedure Swap_B (X, Y : in out Integer) is separate;

   procedure Swap_C (X, Y : in out Integer) is separate;
   --  We don't actually have a body.

   procedure Test_01 (X, Y : in out Integer)
   with Global => null,
        Depends => ((X, Y) =>+ null)
   is
   begin
      Swap_A (X, Y);
      Swap_B (X, Y);
   end Test_01;

   procedure Test_02 (X, Y : in out Integer)
   with Global => null
   is
   begin
      Swap_C (X, Y);
   end Test_02;

end A;
