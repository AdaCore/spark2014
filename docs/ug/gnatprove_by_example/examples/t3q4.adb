package body T3Q4
is
   pragma SPARK_Mode;

   -- Summed_Between is needed for proof purposes only
   function Summed_Between (A : in ArrayType;
                            L, U : in IndexType) return SumType
    with Pre  => (L <= U),
         Post => (Summed_Between'Result <= (U - L + 1) * 1000);

   function Summed_Between (A : in ArrayType;
                            L, U : in IndexType) return SumType is
      (if (L = U) then A(L)
       elsif (L < U) then Summed_Between (A, L, U - 1) + A (U)
       else 0);

   function SumArray (A : in ArrayType) return SumType
   is
      Sum : SumType := 0;
   begin
      for I in IndexType loop
        pragma Loop_Invariant
          ((if I /= IndexType'First then
             Sum = Summed_Between(A, IndexType'First, I - 1)) and
           Sum <= 1000 * (I - IndexType'First));
        Sum := Sum + A (I);
     end loop;
     return Sum;
   end SumArray;

end T3Q4;
