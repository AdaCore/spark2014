package P2
  with SPARK_Mode => On
is
   -- Cases for initialization of package state where
   -- the package is nested inside a subprogram body
   -- and the initialization depends on local variables
   -- of the enclosing subprogram.
   --
   -- See the bodies for commentary on each case.

   procedure E (Y : out Integer)
     with Depends => (Y => null);

   procedure F (Y : out Integer)
     with Depends => (Y => null);
end P2;
