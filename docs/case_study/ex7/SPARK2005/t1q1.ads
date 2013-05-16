package T1Q1
is

  procedure Increment (X: in out Integer);
  --# derives X from X;
  --# pre  X < Integer'Last;
  --# post X = X~ + 1;

end T1Q1;
