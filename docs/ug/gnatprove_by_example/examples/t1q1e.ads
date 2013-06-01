package T1Q1E
is

  procedure Increment (X: in out Integer)
    with Pre => X < Integer'Last,
         Post => X = X'Old + 1;

  procedure Add2 (X : in out Integer)
    with Pre => X <= Integer'Last - 2,
         Post => X = X'Old + 2;

end T1Q1E;
