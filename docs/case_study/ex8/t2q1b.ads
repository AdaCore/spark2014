package T2Q1b
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  procedure Swap (A: in out ArrayType; I, J: in IndexType);
  --  with Post => (A = A'Old'Update (I => A'Old (J), J => A'Old (I)));
  --# derives A from A, I, J;
  --# post A = A~[I => A~(J); J => A~(I)];

end T2Q1b;
