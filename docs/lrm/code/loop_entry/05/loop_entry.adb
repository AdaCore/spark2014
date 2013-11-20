package body Loop_Entry
is

  procedure Clear (A: in out ArrayType; L,U: in IndexType)
  is
  begin
    for I in IndexType range L..U loop
      A(I) := 0;
      --# assert (for all N in IndexType range L..I => (A(N) = 0)) and
      --#        (for all N in IndexType => ((N<L or N>I) -> A(N) = A~(N))) and
      --#        U = U% and L <= I;
      -- Note U = U% is required to show that the vaule of U does not change
      -- within the loop.
    end loop;
  end Clear;

end Loop_Entry;
