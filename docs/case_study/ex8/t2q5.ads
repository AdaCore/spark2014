package T2Q5
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  --  function The_Max(A: ArrayType;
  --                   L, U: IndexType) return ElementType is
  --     ((for all N in IndexType range L..U => (A(N) <= The_Max'Result)) and
  --        (for some N in IndexType range L..U => (A(N) = The_Max'Result)));

  function The_Max(A: ArrayType;
                   L, U: IndexType) return ElementType
    with Post => ((for all N in IndexType range L..U => (A(N) <= The_Max'Result)) and
                    (for some N in IndexType range L..U => (A(N) = The_Max'Result)));

  --# function The_Max(A: ArrayType;
  --#                  L, U: IndexType) return ElementType;
  --# return Max => (for all N in IndexType range L..U => (A(N) <= Max))
  --#   and  (for some N in IndexType range L..U => (A(N) = Max));
  --| Definition:
  --| X = the_max(A, L, U) <->
  --|   (for all N in IndexType range L..U =>
  --|     (element(A, [N]) <= X)) and
  --|   (for some N in IndexType range L..U =>
  --|     (element(A, [N]) = X)).
  --| Properties:
  --| the_max(A, L, L) = element(A, [L]) may_be_deduced.
  --| the_max(A, L, U+1) = X may_be_deduced_from
  --|   [the_max(A, L, U) = X, element(A, [U+1]) <= X].
  --| the_max(A, L, U+1) = element(A, [U+1]) may_be_deduced_from
  --|   [the_max(A, L, U) = X, X <= element(A, [U+1])].

  procedure MaxElement_P1B1 (A: in ArrayType; Max: out ElementType)
    with Post => ((for all N in IndexType => (A(N) <= Max)) and
                    (for some N in IndexType => (A(N) = Max)));
  --# derives Max from A;
  --# post (for all N in IndexType => (A(N) <= Max))
  --#  and (for some N in IndexType => (A(N) = Max));

  procedure MaxElement_P2B1 (A: in ArrayType; Max: out ElementType)
    with Post => (Max = The_Max(A, IndexType'First, IndexType'Last));
  --# derives Max from A;
  --# post Max = The_Max(A, IndexType'First, IndexType'Last);

  procedure MaxElement_P3B1 (A: in ArrayType; Max: out ElementType);
  --# derives Max from A;

  procedure MaxElement_P1B2 (A: in ArrayType; Max: out ElementType)
    with Post => ((for all N in IndexType => (A(N) <= Max)) and
                    (for some N in IndexType => (A(N) = Max)));
  --# derives Max from A;
  --# post (for all N in IndexType => (A(N) <= Max))
  --#  and (for some N in IndexType => (A(N) = Max));

  procedure MaxElement_P2B2 (A: in ArrayType; Max: out ElementType)
    with Post => (Max = The_Max(A, IndexType'First, IndexType'Last));
  --# derives Max from A;
  --# post Max = The_Max(A, IndexType'First, IndexType'Last);

  procedure MaxElement_P3B2 (A: in ArrayType; Max: out ElementType);
  --# derives Max from A;

  procedure MaxElement_P1B3 (A: in ArrayType; Max: out ElementType)
    with Post => ((for all N in IndexType => (A(N) <= Max)) and
                    (for some N in IndexType => (A(N) = Max)));
  --# derives Max from A;
  --# post (for all N in IndexType => (A(N) <= Max))
  --#  and (for some N in IndexType => (A(N) = Max));

end T2Q5;
