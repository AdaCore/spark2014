package body T3Q1
is

  procedure Swap (A: in out ArrayType; I, J: in IndexType)
    with Post => (A(I) = A'Old(J) and A(J) = A'Old(I) and
                    (for all N in IndexType => (if (N/=I and N/=J) then A(N) = A'Old(N))));

  procedure Swap (A: in out ArrayType; I, J: in IndexType)
  --# derives A from A, I, J;
  --# pre  I /= J;
  --# post A(I) = A~(J) and A(J) = A~(I) and
  --#      (for all N in IndexType => ((N/=I and N/=J) -> A(N) = A~(N)));
  is
    T: ElementType;
  begin
    T    := A(I);
    A(I) := A(J);
    A(J) := T;
  end Swap;

  procedure Rotate3(A: in out ArrayType; X, Y, Z: in IndexType)
  is
  begin
    Swap(A, X, Y);
    Swap(A, Y, Z);
  end Rotate3;

end T3Q1;
