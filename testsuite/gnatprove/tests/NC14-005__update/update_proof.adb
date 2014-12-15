procedure Update_Proof
with
   SPARK_Mode
is
   type A_T is array (1..2) of Integer;
   type B_T is array (1..2) of A_T;
begin
   declare
      A : A_T := (1 => 1, 2 => 2);
      O_A : constant A_T := A;
   begin
      A(2) := 0;

      pragma Assert (A (1) = O_A (1));         -- A (1) is unchanged
      pragma Assert (A (2) = 0);               -- A (2) is zero
      pragma Assert (A = O_A'Update (2 => 0)); -- The update assertion is OK
   end;

   declare
      B : B_T :=
        (1 => (1 => 11, 2 => 12),
         2 => (1 => 21, 2 => 22));
      O_B : constant B_T := B;
   begin
      B(2) := (others => 0);

      pragma Assert (B (1) = O_B (1));           -- B (1) is unchanged
      pragma Assert (B (2) = A_T'(others => 0)); -- B (2) is zero
      pragma Assert (B = O_B'Update (2 => (others => 0))); --@ASSERT:PASS
         -- The update assertion fails to prove with timeout = 500

      pragma Assert
        (for all I in 1 .. 2 => (B (I) =
           (if I = 2 then
               A_T'(others => 0)
            else
               O_B (I)))); -- Doing it manually works.
   end;

end Update_Proof;
