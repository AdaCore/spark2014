package body Test is

   subtype Fruits is Natural;

   -----------------------
   --  Nested Generics  --
   -----------------------

   package body External_Generic is
      procedure Fill_Empty_Slots (Inventory : in out Inventory_T;
                                  Fill_With : in     Item_T) is
      begin
         for I in Inventory'Range loop
            if Is_Empty (Inventory (I)) then
               Inventory (I) := Fill_With;
            end if;
         end loop;
      end Fill_Empty_Slots;

   end External_Generic;

   function Found_None (Fruit : in Fruits) return Boolean is (Fruit = 0);

   type Fruit_Crate is array (Positive range <>) of Fruits;

   package Fruit_Crates is new External_Generic (Item_T      => Fruits,
                                                 Inventory_T => Fruit_Crate,
                                                 Is_Empty    => Found_None);

end Test;
