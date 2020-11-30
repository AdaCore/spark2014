package Test is

   --  Nested_Generics  --

   generic
      type Item_T      is private;
      type Inventory_T is array (Positive range <>) of Item_T;
      with function Is_Empty (X : Item_T) return Boolean;
   package External_Generic is
      procedure Fill_Empty_Slots (Inventory : in out Inventory_T;
                                  Fill_With : in     Item_T)
        with Depends => (Inventory =>+ Fill_With),
             Pre     => (Inventory'First < Inventory'Last),
             Post    => (for all I in Inventory'Range =>
                           not Is_Empty (Inventory (I)));

   end External_Generic;
end Test;
