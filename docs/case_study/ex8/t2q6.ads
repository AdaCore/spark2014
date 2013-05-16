package T2Q6
is

  subtype ElementType is Natural range 0..1000;
  subtype CountType is Natural range 0..100;
  subtype IndexType is CountType range CountType'First+1..CountType'Last;
  type ArrayType is array (IndexType) of ElementType;
  subtype SumType is Natural range 0..100000;

  function Sum_Between(A: ArrayType;
                       L: IndexType;
                       U: CountType) return SumType is
     (if (L = U) then A(U)
      elsif (L < U) then Sum_Between (A, L, U - 1) + A (U)
      else ElementType'Last * (L - U));

  --# function Sum_Between(A: ArrayType;
  --#                      L: IndexType;
  --#                      U: CountType) return SumType;
  --# return Sum => ((L = U -> Sum = A(U)) and
  --#                  (L < U -> Sum = Sum_Between (A, L, U - 1) + A (U)) and
  --#                  (L > U -> Sum >= ElementType'Last * (L - U)));

  procedure SumArray (A: in ArrayType; Sum: out SumType)
    with Post => (Sum = Sum_Between(A, IndexType'First, IndexType'Last));
  --# derives Sum from A;
  --# post Sum = Sum_Between(A, IndexType'First, IndexType'Last);

  procedure SumArray_Shift (A: in ArrayType; Shift : in ElementType; Sum: out SumType)
    with Post => (Sum = Sum_Between(A, IndexType'First, IndexType'Last));
  --# derives Sum from A, Shift;
  --# post Sum = Sum_Between(A, IndexType'First, IndexType'Last);

end T2Q6;
