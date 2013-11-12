with Fruit.Priv_Child;

package body Fruit.Pub_Child
  with Refined_State => (Fruit_Salad => (Apples_In_Fruit_Salad,
                                         Oranges_In_Fruit_Salad))
is
   procedure Make_All_Fruit_Salads (Fruit_Salads_Made : out Natural)
     with Refined_Global  => (In_Out => Fruits,
                              Input  => (Apples_In_Fruit_Salad,
                                         Oranges_In_Fruit_Salad)),
          Refined_Depends => (Fruit_Salads_Made => (Fruits,
                                                    Apples_In_Fruit_Salad,
                                                    Oranges_In_Fruit_Salad),
                              Fruits            => (Fruits,
                                                    Apples_In_Fruit_Salad,
                                                    Oranges_In_Fruit_Salad))
   is
   begin
      Fruit_Salads_Made :=
        (if Number_Of_Apples / Apples_In_Fruit_Salad <=
              Number_Of_Oranges / Oranges_In_Fruit_Salad
         then
            Number_Of_Apples / Apples_In_Fruit_Salad
         else
            Number_Of_Oranges / Oranges_In_Fruit_Salad);

      Consume_Apples (Fruit_Salads_Made * Apples_In_Fruit_Salad);
      Consume_Oranges (Fruit_Salads_Made * Oranges_In_Fruit_Salad);
   end Make_All_Fruit_Salads;

   function Price_Of_Fruit_Salad return Natural is
     (if Fruit.Priv_Child.Get_Price_Of_Apple >=
        Fruit.Priv_Child.Get_Price_Of_Orange
      then
         Fruit.Priv_Child.Get_Price_Of_Apple *
           (Apples_In_Fruit_Salad + Oranges_In_Fruit_Salad)
      else
         Fruit.Priv_Child.Get_Price_Of_Orange *
           (Apples_In_Fruit_Salad + Oranges_In_Fruit_Salad))
     with Refined_Global => (Fruits,
                             Apples_In_Fruit_Salad,
                             Oranges_In_Fruit_Salad);
end Fruit.Pub_Child;
