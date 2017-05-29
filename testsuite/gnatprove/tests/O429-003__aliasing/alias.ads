package Alias
  with SPARK_Mode
is
   G : Integer := 5;
   procedure P (X : in out Integer)
     with Global => G;
   procedure Q (X : Integer)
     with Global => (In_Out => G);

   type R (D : Boolean := True) is record
      F : Integer;
   end record;
   H : R;
   procedure P (X : in out R)
     with Global => H;
   procedure Q (X : R)
     with Global => (In_Out => H);

   type A is array (Positive range <>) of Natural;
   C : constant Integer := G;
   I : A (1 .. C);
   procedure P (X : in out A)
     with Global => I;
   procedure Q (X : A)
     with Global => (In_Out => I);

   type B is array (Positive range 1 .. 5) of Natural;
   J : B;
   procedure P (X : in out B)
     with Global => J;
   procedure Q (X : B)
     with Global => (In_Out => J);

   procedure Test;
end Alias;
