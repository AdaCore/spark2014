package body Arith is

   function Sum (X, Y : Integer) return Integer
     with SPARK_Mode => Off
   is
   begin
      return X + Y;
   end Sum;

   function Sum2 (X, Y : Integer) return Integer
     with SPARK_Mode => Off
   is
   begin
      return X + Y;
   end Sum2;

   function Sum_Array (X, Y : Int_Array) return Int_Array is
      Z : Int_Array;
   begin
      for J in Index loop
         Z(J) := X(J) + Y(J);
      end loop;
      return Z;
   end Sum_Array;

   function Sum_Array2 (X, Y : Int_Array) return Int_Array
     with SPARK_Mode => Off
   is
      Z : Int_Array;
   begin
      for J in Index loop
         Z(J) := X(J) + Y(J);
         pragma Loop_Invariant (for all K in 1 .. J => Z(K) = X(K) + Y(K));
      end loop;
      return Z;
   end Sum_Array2;

end Arith;
