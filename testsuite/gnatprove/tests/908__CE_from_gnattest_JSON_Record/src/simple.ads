package Simple
with SPARK_Mode
is

   type Lifetime is range 0 .. 120;

   type People is record
      Age     : Lifetime;
      Height : Natural;
      Name : String (1 .. 3);
   end record;

   function Sum_People (Alice, Bob : People) return Lifetime;

   type Population is array (0 .. 20) of People;

   type Town is record
      Name   : String (1 .. 15);
      People : Population;
   end record;

   procedure Check_Town (T : Town);

   type Int_Array is array (Positive range <>) of Integer;

   type My_Record (Size : Positive) is record
      Data : Int_Array (1 .. Size);
   end record;

   procedure Check_Record (R : My_Record);

end Simple;
