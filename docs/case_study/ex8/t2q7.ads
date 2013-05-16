package T2Q7
is

  subtype ElementType is Natural range 0..1000;
  subtype IndexType is Positive range 1..100;
  type ArrayType is array (IndexType) of ElementType;

  procedure Find (A: in ArrayType; Value: in ElementType;
                  Found: out Boolean; Index: out IndexType)
    with Post => ((Found = (for some N in IndexType => (A(N) = Value))) and
                    (if Found then (A(Index) = Value and
                                      (for all N in IndexType range 1..Index-1 => (A(N) /= Value)))) and
                    (if (not Found) then Index = IndexType'Last));
  --# derives Found, Index from A, Value;
  --# post (Found <-> (for some N in IndexType => (A(N) = Value))) and
  --#      (Found -> (A(Index) = Value and
  --#                 (for all N in IndexType range 1..Index-1 => (A(N) /= Value)))) and
  --#      (not Found -> Index = IndexType'Last);

end T2Q7;
