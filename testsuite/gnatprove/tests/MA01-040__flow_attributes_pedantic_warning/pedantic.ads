with System;
package Pedantic
is
   type R is record
      F1 : Integer;
   end record;

   type A is array (Boolean) of R;

   V : R := R'(F1 => 0);

   C : constant Natural := R'Alignment;

   type T is range 1 .. 10;
   C2 : constant Natural := T'Alignment; -- static

   function Alignment_Of_R return Natural;

   function Order_Of_R return System.Bit_Order;

   function CS_Of_A return Natural;

   function First_Bit_Of_F1 return Natural;

   function Last_Bit_Of_F1 return Natural;

   function Position_Of_F1 return Natural;

   function Size_Of_A return Natural;

   function Size_Of_V return Natural;

end Pedantic;
