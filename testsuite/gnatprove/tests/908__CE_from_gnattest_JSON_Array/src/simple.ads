package Simple
with SPARK_Mode
is

   type T is range 0 .. 10;

   type Index is range 0 .. 10;

   type My_Array is array (Index) of T;

   function Add_Array (A : My_Array) return T;

   type Lifetime is range 0 .. 120;

   type People is record
      Age     : Lifetime;
      Height : Natural;
      Name : String (1 .. 3);
   end record;

   type Family is array (Index) of People;

   procedure Check_Family (F : Family);

end Simple;
