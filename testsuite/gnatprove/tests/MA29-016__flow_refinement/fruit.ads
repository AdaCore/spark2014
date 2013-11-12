package Fruit
  with Abstract_State => Fruits,
       Initializes    => Fruits
is
   function Number_Of_Apples return Natural
     with Global => Fruits;

   function Number_Of_Oranges return Natural
     with Global => Fruits;

   procedure Consume_Apples (Apples_To_Consume : Natural)
     with Global  => (In_Out =>  Fruits),
          Depends => (Fruits =>+ Apples_To_Consume),
          Pre     => Apples_To_Consume <= Number_Of_Apples;

   procedure Consume_Oranges (Oranges_To_Consume : Natural)
     with Global  => (In_Out =>  Fruits),
          Depends => (Fruits =>+ Oranges_To_Consume),
          Pre     => Oranges_To_Consume <= Number_Of_Oranges;

   function Number_Of_Fruits return Natural is
     (Number_Of_Apples + Number_Of_Oranges)
     with Global => Fruits;

   procedure Get_More_Apples
     with Global  => (In_Out => Fruits),
          Depends => (Fruits => Fruits);

   procedure Get_More_Oranges
     with Global  => (In_Out => Fruits),
          Depends => (Fruits => Fruits);

   procedure Increase_Prices
     with Global  => (In_Out => Fruits),
          Depends => (Fruits => Fruits);
private
   Apples  : Natural := 0
     with Part_Of => Fruits;

   Oranges : Natural := 0
     with Part_Of => Fruits;

   Price_Of_Apple  : Natural := 1
     with Part_Of => Fruits;

   Price_Of_Orange : Natural := 1
     with Part_Of => Fruits;
end Fruit;
