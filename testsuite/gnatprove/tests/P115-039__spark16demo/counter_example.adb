package body Counter_Example is

   function Pick_Last (Cat : Category) return Natural is (Num_Item_Per_Category (Cat));

   function Get_Best_Item (Cat1, Cat2 : Category) return Item is
      Idx1  : constant Natural := Pick_Last (Cat1);
      Idx2  : constant Natural := Pick_Last (Cat2);
      Pick1 : Boolean := False;
   begin
      --  compare item of category 1 with item of category 2
      --  set Pick1 to False if item of category 2 is best
      if Pick1 then
         return Item'(Cat => Cat1, Idx => Idx1);
      else
         return Item'(Cat => Cat1, Idx => Idx2);
      end if;
   end Get_Best_Item;

end Counter_Example;
