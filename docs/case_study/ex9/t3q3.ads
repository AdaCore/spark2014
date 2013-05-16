package T3Q3
is

  procedure DoNothing (X, Y: in out Natural)
    with Pre => (Y > 0 and X >= Y),
    Post => (X = X'Old and Y = Y'Old);
  --# derives X from X & Y from Y;
  --# pre  Y > 0 and X >= Y;
  --# post X = X~ and Y = Y~;

end T3Q3;
