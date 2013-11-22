pragma SPARK_Mode (On);
package body Loop_Entry
is

  procedure Clear (A: in out ArrayType; L,U: in IndexType)
  is
  begin
    for I in IndexType range L..U loop
      A(I) := 0;
         pragma Loop_Invariant ((for all N in L..I => (A(N) = 0)) and
           (for all N in IndexType =>
              (if N < L or N > I then A(N) = A'Loop_Entry(N))));
      -- Note it is not necessary to show that the vaule of U does not change
      -- within the loop.
      -- However 'Loop_Entry must be used rather than 'Old.
    end loop;
  end Clear;

end Loop_Entry;
