with Sat;

package Pricing
  with SPARK_Mode
is
   ----------------------------------------------------
   --         SPARK 2014 - Pricing Example           --
   --                                                --
   -- This example illustrates the use of Ada2012's  --
   -- quantifiers in contracts and loop invariants   --
   ----------------------------------------------------

   --  An Item has a Price and a Number occurring
   type Item is record
      Price  : Sat.My_Int;
      Number : Sat.My_Int;
   end record;

   function Price_Of_Item (It : Item) return Sat.My_Int with
     Post => Price_Of_Item'Result = Sat.Mult (It.Price, It.Number);

   --  A Basket is a set of Items
   type Basket is array (Positive range <>) of Item;

   --  The price of a basket.  Note the use of quantification
   --  over the Range of Bk, which is an unconstrained array
   function Price_Of_Basket (Bk : Basket) return Sat.My_Int with
     Post => (for all It in Positive range Bk'Range =>
                Price_Of_Basket'Result >= Price_Of_Item (Bk (It)));

end Pricing;
