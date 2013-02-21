package Other is

   procedure Swap_With_Contract (X, Y : in out Integer)
   with Depends => (X => Y,
                    Y => X);

   procedure Swap_Without_Contract (X, Y : in out Integer);

end Other;
