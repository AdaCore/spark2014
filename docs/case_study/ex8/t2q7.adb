package body T2Q7
is

  procedure Find (A: in ArrayType; Value: in ElementType;
                  Found: out Boolean; Index: out IndexType)
  is
  begin
    Index := IndexType'First;
    Found := False;
    loop
      pragma Loop_Invariant (not Found and
                       Index in IndexType'First..IndexType'Last and
                       (for all N in IndexType range 1..(Index-1) => (A(N) /= Value)));
      Found := A(Index) = Value;
      exit when Found or Index = IndexType'Last;
      --# assert not Found and
      --#        Index in IndexType'First..IndexType'Last-1 and
      --#        (for all N in IndexType range 1..Index => (A(N) /= Value));
      Index := Index + 1;
    end loop;
  end Find;

end T2Q7;
