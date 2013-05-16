package T1Q6
is

  procedure Raise_To_Power(X: in Integer; Y: in Natural; Z: out Integer)
    with Pre => (X ** Y in Integer),
    Post => (Z = X ** Y);
  --# derives Z from X, Y;
  --# pre  X ** Y in Integer;
  --# post Z = X ** Y;

end T1Q6;
