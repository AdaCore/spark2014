package Test is
   --  Generic subprograms

   --  Exchange  --

   generic
      type Item_T is private;
   procedure Exchange (U, V : in out Item_T)
     with Depends => (U => V,
                      V => U);

   --  Generic packages

   --  On_Vectors  --

   generic
      type Item_T   is private;
      type Vector_T is array (Positive range <>) of Item_T;
      with function "+" (X, Y : Item_T) return Item_T;
   package On_Vectors is
      procedure Sum (A, B : in     Vector_T;
                     C    : in out Vector_T)
        with Depends => (C =>+ (A, B)),
             Pre => A'First = C'First and
                    A'Last  = C'Last  and
                    A'Length = B'Length;
   end On_Vectors;

   --  On_Records  --

   generic
      type Item_T is private;
   package On_Records is
      type Array_Of_Items_T is array (1 .. 5) of Item_T;

      type Record_T (D : Natural := 0) is record
         case D is
            when 1 =>
               Single_Item : Item_T;
            when 2 =>
               A, B : Item_T;
            when others =>
               Arr : Array_Of_Items_T;
         end case;
      end record;

      procedure Copy_One_Item (Rec1 : in     Record_T;
                               Rec2 : in out Record_T)
        with Depends => (Rec2 =>+ Rec1),
             Pre     => Rec1.D = Rec2.D;
   end On_Records;

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

      generic
         type New_Item_T is private;
         type New_Inventory_T is array (Positive range <>) of New_Item_T;
         with function Equivalent (Item : Item_T) return New_Item_T;
      package Internal_Generic is
         procedure Replace_Items (Old_Inventory : in     Inventory_T ;
                                  New_Inventory : in out New_Inventory_T;
                                  New_Content   : in     New_Item_T)
           with Pre     => Old_Inventory'First = New_Inventory'First and
                           Old_Inventory'Last  = New_Inventory'Last,
                Depends => (New_Inventory =>+ (Old_Inventory, New_Content));
      end Internal_Generic;
   end External_Generic;
end Test;
