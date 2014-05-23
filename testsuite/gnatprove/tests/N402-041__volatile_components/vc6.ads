package VC6
  with SPARK_Mode => On
is
   type I is range 1 .. 10;

   type A1 is array (I) of Integer
     with Volatile_Components;

   -- V0 OK and should have all Async_* and Effective_*
   -- aspects True by default
   V0 : A1;

   -- V1 should be OK with exactly Async_Writers = True
   -- and other volatile aspects False
   V1 : A1 with Async_Writers;

   -- V2 should be OK with exactly Async_Writers = True
   -- and other volatile aspects False
   V2 : A1 with Async_Writers => True;

   -- V3 OK and should have all Async_* and Effective_*
   -- aspects True by default
   V3 : array (I) of Integer
     with Volatile_Components;

   -- V4 should be OK with exactly Async_Writers = True
   -- and other volatile aspects False
   V4 : array (I) of Integer
     with Volatile_Components, Async_Writers;

   -- V5 should be OK with exactly Async_Writers = True
   -- and other volatile aspects False
   V5 : array (I) of Integer
     with Volatile_Components, Async_Writers => True;

end VC6;
