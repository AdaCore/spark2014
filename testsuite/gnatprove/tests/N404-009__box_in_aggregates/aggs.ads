package Aggs
  with SPARK_Mode => On
is
   type I is range 1 .. 5;

   --  T1 has a default value
   type T1 is range 1 .. 10
     with Default_Value => 5;

   type P1 is private;

   --  T2 does NOT have a default value
   type T2 is range 11 .. 20;

   type A1 is array (I) of T1;

   --  A2 has a default component value
   type A2 is array (I) of T2
     with Default_Component_Value => 20;

   type AP1 is array (I) of P1;

   procedure Init1 (X : out A1)
     with Depends => (X => null);

   procedure Init2 (X : out A2)
     with Depends => (X => null);

   procedure Init3 (X : out AP1)
     with Depends => (X => null);

private
   type P1 is range 1 .. 10
     with Default_Value => 5;
end Aggs;
