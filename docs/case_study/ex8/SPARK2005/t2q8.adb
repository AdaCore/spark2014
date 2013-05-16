package body T2Q8
is

  procedure CreateFibArray (A: out FibArrayType)
  is
  begin
    A := FibArrayType'(others => 1);
    --# assert A(1) = fib(1) and A(2) = fib(2);
    for I in IndexType range 3 .. IndexType'Last loop
      A(I) := A(I-1) + A(I-2);
      --# assert A(1) = 1 and A(2) = 1 and I >= 3 and
      --#   fib(1) = 1 and fib(2) = 1 and
      --#   (for all N in IndexType range 3..I =>
      --#      (A(N) = fib(N) and A(N) >= 1 and
      --#         A(N) <= 2**(N-2)));
    end loop;
  end CreateFibArray;

  procedure CreateFibArray_RTConly (A: out FibArrayType)
  is
  begin
     A := FibArrayType'(others => 1);
     --# assert A(1) = fib(1) and A(2) = fib(2);
    for I in IndexType range 3 .. IndexType'Last loop
      A(I) := A(I-1) + A(I-2);
      --# assert A(1) = 1 and A(2) = 1 and I >= 3 and
      --#   fib(1) = 1 and fib(2) = 1 and
      --#   (for all N in IndexType range 3..I =>
      --#      (1 <= A(N) and A(N) <= 2**(N-2)));
    end loop;
  end CreateFibArray_RTConly;

end T2Q8;
