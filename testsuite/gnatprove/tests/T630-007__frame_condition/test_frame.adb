procedure Test_Frame with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;
   A : constant Nat_Array := (1, 2, 3);

   B : Nat_Array (1 .. 100) := (others => 0);
begin
   for F in reverse 1 .. 98 loop
      pragma Loop_Invariant
        (for all I in ((F + 3) / 4) * 4 .. 100 => B (I) = I mod 4);
      if F mod 4 = 1 then
         B (F .. F + 2) := A;
      end if;
   end loop;
   pragma Assert (for all I in B'Range => B (I) = I mod 4);
end Test_Frame;
