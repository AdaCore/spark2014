package T2Q4
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  procedure Clear (A: in out ArrayType; L,U: in IndexType)
    with Post => ((for all N in IndexType range L..U => (A(N) = 0)) and
                    (for all N in IndexType => (if (N<L or N>U) then A(N) = A'Old(N))));
  --# derives A from A, L, U;
  --# post (for all N in IndexType range L..U => (A(N) = 0)) and
  --#      (for all N in IndexType => ((N<L or N>U) -> A(N) = A~(N)));

end T2Q4;
