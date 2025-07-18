package body Simple
with SPARK_Mode
is

   function Foo (X, Y : T) return T is
   begin
      return X + Y;
   end Foo;

   function Bar (X, Y : T) return T is
   begin
      return X * Y;
   end Bar;

   function Sum_People (Alice, Bob : People) return Lifetime is
   begin
      --  pragma Assert (Alice.Name /= "Bob");
      pragma Assert (Alice.Height /= Bob.Height);
      return Alice.Age + Bob.Age;
   end Sum_People;

   function Div_Float (N : Float) return Float is
   begin
      return 1.0 / (N - 3.1415);
   end Div_Float;

   function Add_Array (A : My_Array) return T is
      Toto : T := 0;
   begin
      for Elt in A'Range loop
         Toto := Toto + A (Elt);
      end loop;
      return Toto;
   end Add_Array;

   function Nested_CE (X, Y : T) return T is
      Z : T;
   begin
      Z := X + Y - 5;
      return Z / Z;
   end Nested_CE;

   procedure Check_Town (T : Town) is
      Total_Age : Integer := 0;
   begin
      for N in T.People'Range loop
         Total_Age := Total_Age + Integer (T.People (N).Age);
      end loop;
      pragma Assert (Total_Age < 420);
   end Check_Town;

   procedure Mammals (A : Animal) is
   begin
      pragma Assert (A /= chicken);
   end Mammals;

   procedure Not_Michel (Name : String) is
   begin
      pragma Assert (Name /= "Michel");
   end;

   procedure Check_Family (F : Family) is
      Total_Age : Integer := 0;
   begin
      for N in F'Range loop
         pragma Assert (F (N).Age /= 22);
      end loop;
   end Check_Family;

   function Sum_List (L : List) return Integer is
      Res : Integer := 0;
   begin
      for I in L'Range loop
         Res := Res + L (I);
      end loop;
      return Res;
   end Sum_List;

   procedure Test_Shape (S : Shape) is
   begin
      pragma Assert (S.Kind = Triangle and then
                     (S.Side1 = S.Side2 and S.Side2 = S.Side3));
   end Test_Shape;

   procedure Check_Record (R : My_Record) is
   begin
      for N in R.Data'Range loop
         pragma Assert (R.Data (N) /= 42);
      end loop;
   end Check_Record;

   procedure Several_Args (A, B, C, D : Integer) is
   begin
      pragma Assert (D mod 2 = 0);
   end Several_Args;

end Simple;
