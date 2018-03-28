package Integer_Fixed is

   type T is delta 2.0 range -10.0 .. 10.0 with Small => 2.0;

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

end Integer_Fixed;
