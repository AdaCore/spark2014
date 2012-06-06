procedure P is
   type Arr is array (Integer range <>) of Integer;

   procedure First is
      My_S1 : Arr (1 .. 3) := (1, 2, 3);
      My_S2 : Arr (2 .. 4) := My_S1;
   begin
      --  This assertion is correct
      pragma Assert (My_S2 (2) = 1);
   end First;

   procedure Second is
      My_S1 : Arr (1 .. 3) := (1, 2, 3);
      My_S2 : Arr (2 .. 4) := My_S1;
   begin
      --  This assertion is not correct
      pragma Assert (My_S2 (2) /= 1);
   end Second;

   procedure Third is
      My_S1 : Arr (1 .. 3) := (1, 2, 3);
      My_S2 : Arr (2 .. 4) := My_S1;
   begin
      --  This assertion is not correct
      pragma Assert (My_S2 (2) = 2);
   end Third;

   procedure Fourth is
      My_S1 : Arr (1 .. 3) := (1, 2, 3);
      My_S2 : Arr (2 .. 4) := My_S1;
   begin
   --  This one is correct
      pragma Assert (My_S2 (2) /= 2);
   end Fourth;

begin
   First;
   Second;
   Third;
   Fourth;
end P;
