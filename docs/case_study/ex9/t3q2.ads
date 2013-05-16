package T3Q2
is

  function Quadruple (X: in Natural) return Natural
    with Pre => (X <= Natural'Last/4),
    Post => (Quadruple'Result = 4 * X);
  --# pre    X <= Natural'Last/4;
  --# return 4 * X;

end T3Q2;
