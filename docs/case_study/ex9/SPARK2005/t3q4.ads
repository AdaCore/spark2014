package T3Q4
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;
  subtype SumType is Natural range 0..100000;

  --# function Summed_Between(A: in ArrayType;
  --#                         L,U: in IndexType) return SumType;
  --# pre L <= U;
  --# return Sum => (((L = U) -> Sum = A(L)) and
  --#                  ((L < U) -> Sum = Summed_Between(A, L, U-1) + A(U)));

  function SumArray (A: in ArrayType) return SumType;
  --# return Summed_Between(A, IndexType'First, IndexType'Last);

end T3Q4;
