package body T2Q1a
is

  procedure Swap (A: in out ArrayType; I, J: in IndexType)
  is
    T: ElementType;
  begin
    T    := A(I);
    A(I) := A(J);
    A(J) := T;
  end Swap;

end T2Q1a;
