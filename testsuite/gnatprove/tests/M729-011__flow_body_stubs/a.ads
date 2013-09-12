package A
is
   

   procedure Swap_A (X, Y : in out Integer)
   with Global  => null,
        Depends => (X => Y,
                    Y => X);

   procedure Swap_B (X, Y : in out Integer)
   with Global  => null,
        Depends => (X => Y,
                    Y => X);

end A;