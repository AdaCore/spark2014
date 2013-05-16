package T1Q2
is

  procedure Increment2 (X, Y: in out Integer);
  --# derives X from X & Y from Y;
  --# pre X /= Integer'Last and Y /= Integer'Last;
  --# post X = X~ + 1 and Y = Y~ + 1;

end T1Q2;
