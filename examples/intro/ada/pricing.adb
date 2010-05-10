package body Pricing is

   function Price_Of_Item (It : Item) return Sat.My_Int is
   begin
      return Sat.Mult (It.Price, It.Number);
   end Price_Of_Item;

   function Price_Of_Basket (Bk : Basket) return Sat.My_Int is
      Total : Sat.My_Int := 0;
   begin
      for It in Positive range Bk'Range loop
         Total := Sat.Add (Total, Price_Of_Item (Bk (It)));
         --# assert for all K in Positive range Bk'First .. It =>
         --#                   (Total >= Price_Of_Item (Bk (K)));
      end loop;
      return Total;
   end Price_Of_Basket;

end Pricing;
