package Simple
with SPARK_Mode
is

   type Lifetime is range 0 .. 120;

   type People is record
      Age     : Lifetime;
      Height : Natural;
      Name : String (1 .. 3);
   end record;

   type T is range 0 .. 10;

   function Foo (X, Y : T) return T
     with Post => Foo'Result < 15;

   function Bar (X, Y : T) return T
     with Post => Bar'Result < 80;

   function Sum_People (Alice, Bob : People) return Lifetime;

   function Div_Float (N : Float) return Float;

   type Index is range 0 .. 10;

   type My_Array is array (Index) of T;

   function Add_Array (A : My_Array) return T;

   function Nested_CE (X, Y : T) return T
     with Pre => X + Y <= 10 and X + Y >= 5;

   type Population is array (0 .. 20) of People;

   type Town is record
      Name   : String (1 .. 15);
      People : Population;
   end record;

   procedure Check_Town (T : Town);

   type Animal is (Cat, Dog, Chicken, Platypus);

   procedure Mammals (A : Animal);

   procedure Not_Michel (Name : String);

   type Family is array (Index) of People;

   procedure Check_Family (F : Family);

   type List is array (Index) of Integer;

   function Sum_List (L : List) return Integer;

   type Shape_Kind_Type is (Square,
                            Triangle,
                            Circle);

   type Shape (Kind : Shape_Kind_Type) is record
      Name : String (1 .. 15);
      case Kind is
         when Square =>
            Side : Natural;
         when Triangle =>
            Side1 : Natural;
            Side2 : Natural;
            Side3 : Natural;
         when others =>
            Perimeter : Natural;
       end case;
   end record;

   procedure Test_Shape (S : Shape);

   type Int_Array is array (Positive range <>) of Integer;

   type My_Record (Size : Positive) is record
      Data : Int_Array (1 .. Size);
   end record;

   procedure Check_Record (R : My_Record);

   procedure Several_Args (A, B, C, D : Integer);

end Simple;
