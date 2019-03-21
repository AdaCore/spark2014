with SPARK.Higher_Order;
with SPARK.Higher_Order.Fold;
package Test_Types with SPARK_Mode is

   package Nested is
      function Id (X : Integer) return Integer;
      pragma Annotate (GNATprove, Terminating, Id);
   private
      pragma SPARK_Mode (Off);
      function Id (X : Integer) return Integer is (X);
   end Nested;
   use Nested;

   Fst : constant Integer := Id (0);
   Lst : constant Integer := Id (100);

   subtype My_Index is Integer range Fst .. Lst;

   type My_Array is array (My_Index range <>) of Integer;

   Fst2 : constant Integer := Id (1);
   Lst2 : constant Integer := Id (200);

   subtype My_Index_2 is Integer range Fst2 .. Lst2;

   type My_Matrix is array (My_Index range <>, My_Index_2 range <>) of Integer;

   subtype Small_Index is Integer range 1 .. 100;

   subtype My_Small is Integer range -100 .. 100;

   type Small_Array is array (Small_Index range <>) of Integer;
   --  There cannot be any overflow in the computation if Result_In_Range does
   --  not overflow.

   type Small_Matrix is array (Small_Index range <>, Small_Index range <>) of Integer;

end Test_Types;
