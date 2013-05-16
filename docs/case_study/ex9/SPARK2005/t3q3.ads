package T3Q3
is

  procedure DoNothing (X, Y: in out Natural);
  --# derives X from X & Y from Y;
  --# pre  Y > 0 and X >= Y;
  --# post X = X~ and Y = Y~;

end T3Q3;
