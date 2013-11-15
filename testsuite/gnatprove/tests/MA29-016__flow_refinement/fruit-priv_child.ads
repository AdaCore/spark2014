private package Fruit.Priv_Child
  with Abstract_State => (Price_Related_Stuff with Part_Of => Fruits),
       Initializes    => Price_Related_Stuff
is
   procedure Increase_Price_Of_Apple
     with Global => (In_Out => Price_Of_Apple);

   procedure Increase_Price_Of_Orange
     with Global => (In_Out => Price_Of_Orange);

   function Get_Price_Of_Apple return Natural is (Price_Of_Apple)
     with Global => Fruits;

   function Get_Price_Of_Orange return Natural is (Price_Of_Orange)
     with Global => Price_Of_Orange;

   procedure Earn_As_Much_Money_As_Possible (Profit : out Natural)
     with Global => (Input  => (Price_Of_Apple,
                                Price_Of_Orange),
                     In_Out => (Apples,
                                Oranges));
private
   Extra_Cost : Natural := 2
     with Part_Of => Price_Related_Stuff;
end Fruit.Priv_Child;
