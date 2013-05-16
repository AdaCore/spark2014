package T2Q1a
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  procedure Swap (A: in out ArrayType; I, J: in IndexType);
  --# derives A from A, I, J;
  --# post A(I) = A~(J) and A(J) = A~(I) and
  --#      (for all N in IndexType => ((N/=I and N/=J) -> A(N) = A~(N)));

end T2Q1a;
