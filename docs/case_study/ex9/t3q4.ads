package T3Q4
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;
  subtype SumType is Natural range 0..100000;

  function Summed_Between(A: in ArrayType;
                          L,U: in IndexType) return SumType
   with Pre  => (L <= U),
        Post => (Summed_Between'Result <= (U - L+1)*1000);

  function Summed_Between(A: in ArrayType;
                          L,U: in IndexType) return SumType is
     (if (L = U) then A(L)
     elsif (L < U) then Summed_Between(A, L, U-1) + A(U)
     else 0);
  --# function Summed_Between(A: in ArrayType;
  --#                         L,U: in IndexType) return SumType;
  --# pre L <= U;
  --# return Sum => (((L = U) -> Sum = A(L)) and
  --#                  ((L < U) -> Sum = Summed_Between(A, L, U-1) + A(U)));

  function SumArray (A: in ArrayType) return SumType;
  --# return Summed_Between(A, IndexType'First, IndexType'Last);

end T3Q4;
