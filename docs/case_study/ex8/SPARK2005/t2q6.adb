package body T2Q6
is

  procedure SumArray (A: in ArrayType; Sum: out SumType)
  is
  begin
    Sum := 0;
    for I in IndexType loop
      Sum := Sum + A(I);
      --# assert Sum = Sum_Between(A, IndexType'First, I)
      --#   and  0 <= Sum
      --#   and  Sum <= ElementType'Last * (I - IndexType'First + 1);
    end loop;
  end SumArray;

  procedure SumArray_Shift (A: in ArrayType; Shift : in ElementType; Sum: out SumType)
  is
  begin
    Sum := Shift;
    for I in IndexType loop
      --# assert ((I /= IndexType'First) -> (Sum = Sum_Between(A, IndexType'First, I-1)))
      --#   and  ((I = IndexType'First) -> (Sum = Shift))
      --#   and  Sum <= Sum_Between(A, IndexType'First, I-1)
      --#   and  0 <= Sum
      --#   and  ((I /= IndexType'First) -> (Sum <= ElementType'Last * (I - IndexType'First)));
       if I = IndexType'First then
          Sum := (Sum - Shift) + A(I);
       else
          Sum := Sum + A(I);
       end if;
      --# assert Sum = Sum_Between(A, IndexType'First, I)
      --#   and  0 <= Sum
      --#   and  Sum <= ElementType'Last * (I - IndexType'First + 1);
    end loop;
  end SumArray_Shift;

end T2Q6;
