package Aggs
  with SPARK_Mode => On
is

   -- TU: 1. The box symbol, <>, may only be used in an aggregate if the type(s)
   --     of the corresponding component(s) define full default initialization.

   type I is range 1 .. 5;

   --  T1 has a default value
   type T1 is range 1 .. 10
     with Default_Value => 5;

   type P1 is private;

   type P2 is private;

   --  T2 does NOT have a default value
   type T2 is range 11 .. 20;

   type A1 is array (I) of T1;

   type AP1 is array (I) of P1;

   type AP2 is array (I) of P2;

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

   procedure Init4 (X : out AP1)
     with Depends => (X => null);

   procedure Init5 (X : out AP2)
     with Depends => (X => null);

private
   type P1 is range 1 .. 10
     with Default_Value => 5;

   type P2 is range 1 .. 10;
end Aggs;
