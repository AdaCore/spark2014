package Port
   with SPARK_Mode => On
is
   -- N110-011 calls for the removal of volatile types for SPARK 2014 rel 1.
   --
   -- This small test case provides evidence that this has been implemented,
   -- BUT this package shows that a volatile record object can still be used
   -- to read a port, using a whole-record assignment.

   type R0 is record
      F1 : Integer;
   end record; -- OK, non-volatile type

   V : R0
     with Volatile, -- volatile object
          Async_Writers;

   procedure Read (X : out Integer)
     with Global => (Input => V),
     Depends => (X => V);

end Port;

