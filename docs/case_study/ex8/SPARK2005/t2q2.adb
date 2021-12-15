package body T2Q2
is

  procedure Clear (A: in out ArrayType; L,U: in IndexType)
  is
  begin
    for I in IndexType range L..U loop
      A(I) := 0;
    end loop;
  end Clear;

end T2Q2;
