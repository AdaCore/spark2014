package body Foo
is

   type Empty_Rec2 (D : Positive := 1) is null record;
   type My_Array2 is array (Positive range <>) of Empty_Rec2;
   type Non_Init2 is record
      E : My_Array2 (1 .. 100);
      F : Natural;
   end record;

   procedure Test_01 (X : out Boolean)
   is
      All_1 : Non_Init2;
   begin
      X := All_1.E (1).D = 1;
   end Test_01;

end Foo;
