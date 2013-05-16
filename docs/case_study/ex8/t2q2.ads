package T2Q2
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  procedure Clear (A: in out ArrayType; L,U: in IndexType);
  --# derives A from A, L, U;

end T2Q2;
