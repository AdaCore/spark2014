package Overloading
is
   --  Default for generic some time it must be good
   --  to overload some opeartion. but SPARK disallow this
   procedure Swap (X, Y : in out Integer);
   procedure Swap (X, Y : in out Float);
   procedure Swap (X, Y : in out Long_Integer);

end Overloading;
