package VC5
  with SPARK_Mode => On
is
   --  N402-041__volatile_components
   --
   --  Tests array types with Volatile_Components
   --  and explicit external aspects

   type I is range 1 .. 10;

   type A2 is array (I) of Integer
     with Volatile_Components;

   type A3 is array (I) of Integer -- illegal - cannot apply to a type
     with Volatile_Components,
          Async_Writers;

   V2 : A2 with Async_Writers; -- OK
   V3 : A2 with Volatile, Async_Writers; -- OK

   S1 : array (I) of Integer; -- OK

   S2 : array (I) of Integer -- illegal - object not volatile
     with Async_Writers;

   S3 : array (I) of Integer -- OK
     with Volatile_Components;

   -- SPARK RM says that Async_Writers can be applied to an
   -- effectively volatile object, so this should be OK
   S4 : array (I) of Integer -- ???
     with Volatile_Components, Async_Writers;

   S5 : array (I) of Integer -- OK
     with Volatile;

   S6 : array (I) of Integer -- OK
     with Volatile, Async_Writers;

   S7 : array (I) of Integer -- OK
     with Volatile, Volatile_Components;

   S8 : array (I) of Integer -- OK
     with Volatile, Volatile_Components, Async_Writers;

end VC5;
