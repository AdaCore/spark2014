package T1Q1
is

  procedure Increment (X: in out Integer)
    with Pre => (X < Integer'Last),
         Post => (X = X'Old + 1);
  --# derives X from X;
  --# pre  X < Integer'Last;
  --# post X = X~ + 1;

end T1Q1;
