package body Fruit.Priv_Child
  with Refined_State => (Price_Related_Stuff => Extra_Cost)
is
   procedure Increase_Price_Of_Apple
   is
   begin
      if Price_Of_Apple <= Natural'Last - Extra_Cost then
         Price_Of_Apple := Price_Of_Apple + Extra_Cost;
      else
         Price_Of_Apple := Natural'Last;
      end if;
   end Increase_Price_Of_Apple;

   procedure Increase_Price_Of_Orange
     with Refined_Global => (Input  => Extra_Cost,
                             In_Out => Price_Of_Orange)
   is
   begin
      if Price_Of_Orange <= Natural'Last - Extra_Cost then
         Price_Of_Orange := Price_Of_Orange + Extra_Cost;
      else
         Price_Of_Orange := Natural'Last;
      end if;
   end Increase_Price_Of_Orange;

   procedure Earn_As_Much_Money_As_Possible (Profit : out Natural) is
      Money        : Natural;
      Fruit_Salads : Natural;
   begin
      --  Make as many fruit salads as possible.
      Make_All_Fruit_Salads (Fruit_Salads);
      Money   := Fruit_Salads * Price_Of_Fruit_Salad;
      --  Sell whatever fruit remains individually.
      Money   := Money + Apples * Get_Price_Of_Apple;
      Money   := Money + Oranges * Get_Price_Of_Orange;
      --  No more fruits remain...
      Apples  := 0;
      Oranges := 0;
      Profit  := Money;
   end Earn_As_Much_Money_As_Possible;
end Fruit.Priv_Child;
