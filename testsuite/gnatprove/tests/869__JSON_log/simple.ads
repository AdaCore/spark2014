package Simple with SPARK_Mode is

   type Lifetime is range 0 .. 120;

   type People is record
      Name : String (1 .. 15);
      Age : Lifetime;
   end record;

   type T is range 0 .. 10;

   function Foo (X, Y : T) return T
     with Post => Foo'Result < 15;

   function Bar (X, Y : T) return T
     with Post => Bar'Result < 80;

   function Sum_People (Alice, Bob : People) return Lifetime;

   function Div_Float (N : Float) return Float;

   type Index is range 0 .. 2;

   type My_Array is array (Index) of T;

   function Add_Array (A : My_Array) return T;

   function Nested_CE (X, Y : T) return T
     with Pre => X + Y <= 10 and X + Y >= 5;

   type F is delta 1.0 / 128.0 range 0.0 .. 255.0;

   function Fixed_Point (X, Y : F) return F;

   function Obvious_Div_By_Zero (N : Integer) return Integer;

   procedure Float_Precision (F : Float);

   type Population is array (0 .. 20) of People;

   type Town is record
      Name : String (1 .. 15);
      People : Population;
   end record;

   procedure Check_Town (T : Town);

   type Animal is (Cat, Dog, Chicken, Platypus);

   procedure Mammals (A : Animal);

   procedure Not_Michel (S : String);
end Simple;
