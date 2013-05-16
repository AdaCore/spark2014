package T1Q5
is

  procedure Bounded_Add(X,Y: in Integer; Z: out Integer)
    with Post => ((if (Integer'First <= X+Y and X+Y <= Integer'Last) then Z=X+Y)
    and (if (Integer'First > X+Y) then Z=Integer'First)
    and (if (X+Y > Integer'Last) then Z=Integer'Last));
  --# derives Z from X, Y;
  --# post ((Integer'First <= X+Y and X+Y <= Integer'Last) -> Z=X+Y)
  --#  and ((Integer'First >  X+Y)                         -> Z=Integer'First)
  --#  and (                         (X+Y >  Integer'Last) -> Z=Integer'Last);

end T1Q5;
