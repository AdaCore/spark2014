package VC4
  with SPARK_Mode => On
is
   --  N402-041__volatile_components
   --
   --  Tests for proof on array types that have Volatile
   --  and/or Volatile_Components

   type I is range 1 .. 10;

   type A0 is array (I) of Integer;

   type A1 is array (I) of Integer
     with Volatile;

   type A2 is array (I) of Integer
     with Volatile_Components;

   type A3 is array (I) of Integer
     with Volatile,
          Volatile_Components;

   V0 : A0;
   V1 : A1;
   V2 : A2 with Volatile;
   V3 : A3;

   -- V4 : A2; -- should this be legal without "with Volatile" on the end?

   procedure F0 (X : in A0; R : out Boolean)
     with Global => (Input => V0),
          Depends => (R => (X, V0));

   procedure F1 (X : in A1; R : out Boolean)
     with Global => (In_Out => V1),
          Depends => (R => (X, V1),
                      V1 => V1);

   procedure F2 (X : in A2; R : out Boolean)
     with Global => (In_Out=> V2),
          Depends => (R => (X, V2),
                      V2 => V2);

   procedure F3 (X : in A3; R : out Boolean)
     with Global => (In_Out => V3),
          Depends => (R => (X, V3),
                      V3 => V3);

end VC4;
