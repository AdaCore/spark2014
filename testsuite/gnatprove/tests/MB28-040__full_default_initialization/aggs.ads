package Aggs
  with SPARK_Mode => On
is

   -- TU: 1. The box symbol, <>, may only be used in an aggregate if the type(s)
   --     of the corresponding component(s) define full default initialization.

   type I is range 1 .. 5;

   --  T1 has a default value
   type T1 is range 1 .. 10
     with Default_Value => 5;

   --  T2 does NOT have a default value
   type T2 is range 11 .. 20;

   type A1 is array (I) of T1;

   type A2 is array (I) of T2;

   --  A3 has a default component value
   type A3 is array (I) of T2
     with Default_Component_Value => 20;

   procedure Init1 (X : out A1)
     with Depends => (X => null);

   procedure Init2 (X : out A2)
     with Depends => (X => null);

   procedure Init3 (X : out A3)
     with Depends => (X => null);

end Aggs;
