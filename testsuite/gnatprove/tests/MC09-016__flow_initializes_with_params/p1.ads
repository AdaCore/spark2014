package P1
  with SPARK_Mode => On
is
   -- Cases for initialization of package state where
   -- the package is nested inside a subprogram body
   -- and the initialization depends on formal
   -- parameters of the enclosing subprogram.
   --
   -- See the bodies for commentary on each case.
   --
   -- These cases all should be legal, but are
   -- currently rejected by FE 7.2.1

   procedure A (X : in     Integer;
                Y :    out Integer)
     with Depends => (Y => X);

   procedure B (X : in out Integer;
                Y :    out Integer)
     with Depends => (Y => X,
                      X => X);

   procedure C (X : out Integer;
                Y : out Integer)
     with Depends => (Y => null,
                      X => null);

   procedure D (X : out Integer;
                Y : out Integer)
     with Depends => (Y => null,
                      X => null);

end P1;
