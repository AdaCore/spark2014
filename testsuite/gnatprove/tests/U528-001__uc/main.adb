with Ada.Unchecked_Conversion;
procedure Main with SPARK_Mode is

   type T is range 1 .. Integer'Last with Size => 31, Object_Size => 32;

   subtype U is T with Object_Size => 32;

   type A is mod 2 ** 32 with Size => 32, Object_Size => 32;

   function UC is new Ada.Unchecked_Conversion (T, A);

begin
   null;
end Main;
