with Fruit.Priv_Child;

package body Fruit
  with Refined_State => (Fruits => (X,
                                    Apples,
                                    Oranges,
                                    Price_Of_Apple,
                                    Price_Of_Orange,
                                    Fruit.Priv_Child.Price_Related_Stuff))
is

   X : Integer;

   function Number_Of_Apples return Natural is (Apples)
     with Refined_Global => Apples;

   function Number_Of_Oranges return Natural is (Oranges)
     with Refined_Global => Oranges;

   procedure Consume_Apples (Apples_To_Consume : Natural)
     with Refined_Global  => (In_Out =>  Apples),
          Refined_Depends => (Apples =>+ Apples_To_Consume)
   is
   begin
      Apples := Apples - Apples_To_Consume;
   end Consume_Apples;

   procedure Consume_Oranges (Oranges_To_Consume : Natural)
     with Refined_Global  => (In_Out  =>  Oranges),
          Refined_Depends => (Oranges =>+ Oranges_To_Consume)
   is
   begin
      Oranges := Oranges - Oranges_To_Consume;
   end Consume_Oranges;

   procedure Get_More_Apples
     with Refined_Global  => (In_Out => Apples),
          Refined_Depends => (Apples => Apples)
   is
   begin
     if Apples < Natural'Last - 5 then
        Apples := Apples + 5;
     else
        Apples := Natural'Last;
     end if;
   end Get_More_Apples;

   procedure Get_More_Oranges
      with Refined_Global  => (In_Out  =>  Oranges),
           Refined_Depends => (Oranges =>+ null)
   is
   begin
      if Oranges < Natural'Last - 10 then
         Oranges := Oranges + 10;
      else
         Oranges := Natural'Last;
      end if;
   end Get_More_Oranges;

   procedure Increase_Prices
     with Refined_Global  => (In_Out => (Price_Of_Apple,
                                         Price_Of_Orange),
                              Input  => Fruit.Priv_Child.Price_Related_Stuff),
          Refined_Depends => ((Price_Of_Apple,
                               Price_Of_Orange) =>+ Fruit.Priv_Child.Price_Related_Stuff)
   is
   begin
      Fruit.Priv_Child.Increase_Price_Of_Apple;
      Fruit.Priv_Child.Increase_Price_Of_Orange;
   end Increase_Prices;
end Fruit;
