procedure Multidim_Array_Init with SPARK_Mode is
   type Arr is array (Positive range <>, Positive range <>) of Integer;
   function Get return Positive with Import, Global => null;

   procedure Read (A : Arr) with Import, Global => null, Always_Terminates;

   function Id (I : Positive) return Positive is (I) with Pre => True;

   A : Arr (1 .. Get, 1 .. Get);
begin
   for I in A'Range loop
      for J in 1 .. Get loop
         A (I, J) := J;
      end loop;
   end loop;

   Read (A);
end Multidim_Array_Init;
