with Sat;
--# inherit Sat;

package Pricing is

   type Item is record
      Price  : Sat.My_Int;
      Number : Sat.My_Int;
   end record;

   function Price_Of_Item (It : Item) return Sat.My_Int;
   --# return Sat.Mult (It.Price, It.Number);

   type Basket is array (Positive range <>) of Item;

   function Price_Of_Basket (Bk : Basket) return Sat.My_Int;
   --# return Price => for all It in Positive range Bk'Range =>
   --#                   (Price >= Price_Of_Item (Bk (It)));

end Pricing;
