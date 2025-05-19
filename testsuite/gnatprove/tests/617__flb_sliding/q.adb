pragma Extensions_Allowed (All);
procedure Q
  with SPARK_Mode
is
   type T is array (Positive range 1 .. <>) of Integer;

   procedure Loc (X : T) is
   begin
      pragma Assert (X(2) = 2);  -- @ASSERT:FAIL
   end Loc;

   Var : T := (1, 2, 3, 4);
begin
   Loc (Var(2 .. 3));
end Q;
