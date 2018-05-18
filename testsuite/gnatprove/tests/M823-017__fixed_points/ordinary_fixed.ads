package Ordinary_Fixed is

   S : constant := 1.0 / 400.0;
   type T is delta S range -10.0 .. 10.0 with Small => S;

   procedure Test_Minus (X : T) with
     Pre => X in -5.0 .. 5.0;

   procedure Test_Add (X : T) with
     Pre => X in -5.0 .. 5.0;

   procedure Test_Subtract (X : T) with
     Pre => X in -5.0 .. 5.0;

   procedure Test_Multiply (X : T) with
     Pre => X in -5.0 .. 5.0;

   procedure Test_Divide (X : T) with
     Pre => X in -5.0 .. 5.0;

   procedure Test_Type_Conversion (X : T) with
     Pre => X in -5.0 .. 5.0;

   procedure Test_Compare (X : T) with
     Pre => X in -5.0 .. 5.0;

end Ordinary_Fixed;
