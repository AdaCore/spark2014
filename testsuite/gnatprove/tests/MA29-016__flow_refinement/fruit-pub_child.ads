package Fruit.Pub_Child
  with Abstract_State => Fruit_Salad,
       Initializes    => Fruit_Salad
is
   procedure Make_All_Fruit_Salads (Fruit_Salads_Made : out Natural)
     with Global  => (In_Out => Fruits,
                      Input  => Fruit_Salad),
          Depends => (Fruit_Salads_Made => (Fruits,
                                            Fruit_Salad),
                      Fruits => (Fruits,
                                 Fruit_Salad));

   function Price_Of_Fruit_Salad return Natural
     with Global => (Fruits,
                     Fruit_Salad);
private
   Apples_In_Fruit_Salad  : Natural := 2
     with Part_Of => Fruit_Salad;
   Oranges_In_Fruit_Salad : Natural := 1
     with Part_Of => Fruit_Salad;
end Fruit.Pub_Child;
