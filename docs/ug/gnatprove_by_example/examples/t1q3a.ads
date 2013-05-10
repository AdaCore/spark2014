package T1Q3A
is

  procedure Swap (X, Y : in out Integer)
   with Post => (X = Y'Old)
                  and then (Y = X'Old);

end T1Q3A;
