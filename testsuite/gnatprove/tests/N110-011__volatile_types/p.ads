package P
  with SPARK_Mode => On
is
   -- N110-011 calls for the removal of volatile types for SPARK 2014 rel 1.
   -- N127-006 reverts this, allowing Volatile types.
   --
   -- This small test case provides evidence that this has been implemented.

   -- scalar, non-volatile
   type T0 is range 1 .. 10; -- OK

   -- scalar, volatile by pragma
   type T1 is range 1 .. 10;
   pragma Volatile (T1);

   -- scalar, volatile by aspect
   type T2 is range 1 .. 10
     with Volatile;


   -- composite, non-volatile
   type R0 is record
      F1 : Integer;
   end record; -- OK

   -- composite, volatile by pragma
   type R1 is record
      F1 : Integer;
   end record;
   pragma Volatile (R1);

   -- composite, volatile by aspect
   type R2 is record
      F1 : Integer;
   end record with Volatile;

end P;
