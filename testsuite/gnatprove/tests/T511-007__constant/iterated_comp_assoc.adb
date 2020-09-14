procedure Iterated_Comp_Assoc with SPARK_Mode is
   type Int_Array is array (Positive range 1 .. 10) of Integer;
   type Int_Array_Array is array (Positive range <>) of Int_Array;

   A : Int_Array_Array := (for I in 1 .. 10 => (1 .. 10 => I));
   pragma Assert (for all K in A'Range => A (K) = (for J in 1 .. 10 => K));
begin
   null;
end Iterated_Comp_Assoc;
