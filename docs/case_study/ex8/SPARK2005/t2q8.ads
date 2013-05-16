package T2Q8
is

  subtype IndexType is Positive range 1..32;
  type FibArrayType is array (IndexType) of Positive;

  --# function fib (I: IndexType) return Positive;
  --# return Result => ((I <= 2 -> Result = 1) and
  --#                     (I > 2 -> Result = Fib(I-1) + Fib(I-2)));

  procedure CreateFibArray (A: out FibArrayType);
  --# derives A from;
  --# post for all N in IndexType => (A(N) = fib(N));

  procedure CreateFibArray_RTConly (A: out FibArrayType);
  --# derives A from;

end T2Q8;
