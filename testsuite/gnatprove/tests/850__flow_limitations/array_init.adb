procedure Array_Init with SPARK_Mode is
   type I_Arr is array (Positive range <>) of Integer;

   procedure Read (A : I_Arr) with Import, Global => null, Always_Terminates;
   function Get return Positive with Import, Global => null;

   function Id (I : Positive) return Positive is (I) with Pre => True;

   A : I_Arr (1 .. Get);
begin
   for I in A'Range loop
      A (I - 1 + 1) := I;
   end loop;

   for I in A'Range loop
      exit when I = 0;
      A (I) := I;
   end loop;

   for I in 2 .. Get loop
      A (I) := I;
   end loop;

   for I in A'Range loop
      A (I) := I;

      pragma Loop_Invariant (for all J in A'First .. I => A (J) = J);
   end loop;

   for I in A'Range loop
      pragma Loop_Invariant (for all J in A'First .. I - 1 => A (J) = J);

      A (I) := I;
   end loop;

   Read (A);
end  Array_Init;
