package body Array_Comparison is

   procedure P is
      X : Natural_Array := (1 .. 10 => 1);
      Y : Natural_Array := (1 .. 9 => 1);
      Z : Natural_Array := (1 .. 5 => 1, 6 => 0, 7 .. 20 => 9);
   begin
      pragma Assert (X > Y);
      pragma Assert (X (1 .. 5) = Z (1 .. 5));
      pragma Assert (X > Z);
      pragma Assert (X < Z);
   end;

end Array_Comparison;
