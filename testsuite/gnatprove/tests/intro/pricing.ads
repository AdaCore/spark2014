pragma SPARK_Mode (On);

with Sat;

package Pricing is

   type Item is record
      Price  : Sat.My_Int;
      Number : Sat.My_Int;
   end record;

   function Price_Of_Item (It : Item) return Sat.My_Int with
     Post => Price_Of_Item'Result = Sat.Mult (It.Price, It.Number);

   type Basket is array (Positive range <>) of Item;

   function Price_Of_Basket (Bk : Basket) return Sat.My_Int with
     Post => (for all It in Positive range Bk'Range =>
                Price_Of_Basket'Result >= Price_Of_Item (Bk (It)));

end Pricing;
