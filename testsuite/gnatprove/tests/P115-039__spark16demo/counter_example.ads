package Counter_Example is

   subtype Category is Positive range 1 .. 8;
   type Num_Item_T is array (Category range <>) of Natural;

   Num_Item_Per_Category : constant Num_Item_T :=
     (1 => 3, 2 => 8, 3 => 10_000, 4 => 42, 5 => 98, 6 => 76, 7 => 0, 8 => 1);

   type Item is record
      Cat : Category;
      Idx : Natural;
   end record with Predicate => Item.Idx <= Num_Item_Per_Category (Item.Cat);

   function Get_Best_Item (Cat1, Cat2 : Category) return Item;

end Counter_Example;
