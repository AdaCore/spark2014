package Other is
   procedure A (N : in out Integer);

   procedure B (N : in out Integer)
   with Global => null;
end Other ;
