pragma SPARK_Mode (On);

package body Pricing is

   function Price_Of_Item (It : Item) return Sat.My_Int is
      (Sat.Mult (It.Price, It.Number));

   function Price_Of_Basket (Bk : Basket) return Sat.My_Int is
      Total : Sat.My_Int := 0;
   begin
      for It in Positive range Bk'Range loop
         pragma Loop_Invariant
           (for all K in Positive range Bk'First .. It - 1 =>
              (Total >= Price_Of_Item (Bk (K))));
         Total := Sat.Add (Total, Price_Of_Item (Bk (It)));
      end loop;
      return Total;
   end Price_Of_Basket;

end Pricing;
