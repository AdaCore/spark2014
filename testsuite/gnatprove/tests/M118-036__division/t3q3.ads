package T3Q3
is

  procedure DoNothing (X, Y: in out Natural)
  with Pre => Y > 0 and X >= 0,
       Post => X = X'Old and Y = Y'Old;

end T3Q3;
