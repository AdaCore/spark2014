package body Test is
   ----------------
   --  Exchange  --
   ----------------

   procedure Exchange (U, V : in out Item_T)
   is
      Temp : Item_T;
   begin
      Temp := U;
      U    := V;
      V    := Temp;
   end Exchange;

   procedure Swap is new Exchange (Item_T => Integer);
   procedure Swap is new Exchange (Item_T => Character);

   procedure Call_Both (A, B : in out Integer;
                        C, D : in out Character)
   is
   begin
      Swap (A, B);
      Swap (C, D);
   end Call_Both;

   ------------------
   --  On_Vectors  --
   ------------------

   package body On_Vectors is
      procedure Sum (A, B : in     Vector_T;
                     C    : in out Vector_T) is
      begin
         for I in A'Range loop
            C (I) := A (I) + B (I + B'First - A'First);
         end loop;
      end Sum;
   end On_Vectors;

   type Table is array (Positive range <>) of Integer;

   package Int_Vectors is new On_Vectors (Item_T   => Integer,
                                          Vector_T => Table,
                                          "+"      => "+");

   procedure Sum_And_Reverse (A, B : in     Table;
                              C    : in out Table)
     with Depends => (C =>+ (A, B)),
          Pre => A'First = C'First and
                 A'Last  = C'Last  and
                 A'Length = B'Length
   is
   begin
      Int_Vectors.Sum (A, B, C);
      for I in C'First .. C'Last / 2 loop
         declare
            Temp : Integer;
         begin
            Temp  := C (I);
            C (I) := C (C'Last - I + C'First);
            C (C'Last - I + C'First) := Temp;
         end;
      end loop;
   end Sum_And_Reverse;

   ------------------
   --  On_Records  --
   ------------------

   package body On_Records is
      procedure Copy_One_Item (Rec1 : in     Record_T;
                               Rec2 : in out Record_T) is
      begin
         if Rec1.D = 1 then
            Rec2.Single_Item := Rec1.Single_Item;
         elsif Rec1.D = 2 then
            Rec2.B := Rec1.B;
         else
            Rec2.Arr (5) := Rec1.Arr (3);
         end if;
      end Copy_One_Item;
   end On_Records;

   type Fruits_And_Weapons is (None, Apple, Orange, Banana, Strawberries,
                               Grapes, Pineapple, Mellon,
                               Watermellon, Fake_Watermellon,
                               Pistol, Knife, Grenade);
   --  subtype Weapons is Fruits_And_Weapons range Pistol .. Grenade;
   subtype Fruits is Fruits_And_Weapons range None  .. Fake_Watermellon;

   package Fruit_Rec is new On_Records (Item_T => Fruits);
   use Fruit_Rec;

   procedure Replace_A_Fruit (Rec1 : in     Record_T;
                              Rec2 : in out Record_T)
     renames Copy_One_Item;

   Apple_Basket : Record_T (0) := (D => 0,
                                   Arr => (Apple,
                                           Apple,
                                           Apple,
                                           Apple,
                                           Apple));
   Mixed_Basket : Record_T := (D => 0,
                               Arr => (Banana,
                                       Strawberries,
                                       Orange,
                                       Grapes,
                                       Pineapple));

   procedure Replace_And_Search_For_Apple (Has_Apple : out Boolean)
     with Global => (Input  => Apple_Basket,
                     In_Out => Mixed_Basket)
   is
   begin
      Replace_A_Fruit (Apple_Basket, Mixed_Basket);
      Has_Apple := False;
      case Mixed_Basket.D is
         when 1 =>
            if Mixed_Basket.Single_Item = Apple then
               Has_Apple := True;
            end if;
         when 2 =>
            if (Mixed_Basket.A = Apple) or (Mixed_Basket.B = Apple) then
               Has_Apple := True;
            end if;
         when others =>
            for I in Mixed_Basket.Arr'Range loop
               if Mixed_Basket.Arr (I) = Apple then
                  Has_Apple := True;
                  return;
               end if;
            end loop;
      end case;
   end Replace_And_Search_For_Apple;

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

      package body Internal_Generic
      is
         procedure Replace_Items (Old_Inventory : in     Inventory_T ;
                                  New_Inventory : in out New_Inventory_T;
                                  New_Content   : in     New_Item_T)
         is
         begin
            for I in Old_Inventory'Range loop
               if Is_Empty (Old_Inventory (I)) then
                  New_Inventory (I) := New_Content;
               else
                  New_Inventory (I) := Equivalent (Old_Inventory (I));
               end if;
            end loop;
         end Replace_Items;
      end Internal_Generic;
   end External_Generic;

   function Found_None (Fruit : in Fruits) return Boolean is (Fruit = None);

   function Fruits_To_Fruits_And_Weapons (Fruit : in Fruits)
                                         return Fruits_And_Weapons
   is (Fruits_And_Weapons (Fruit));

   type Fruit_Crate             is array (Positive range <>) of Fruits;
   type Fruit_And_Weapons_Crate is array (Positive range <>) of Fruits_And_Weapons;

   package Fruit_Crates is new External_Generic (Item_T      => Fruits,
                                                 Inventory_T => Fruit_Crate,
                                                 Is_Empty    => Found_None);
   use Fruit_Crates;

   procedure Weapon_Smuggling (Initial_Crate : in out Fruit_Crate;
                               Final_Crate   : in out Fruit_And_Weapons_Crate)
     with Pre     => Initial_Crate'First = Final_Crate'First and
                     Initial_Crate'Last  = Final_Crate'Last,
          Depends => (Initial_Crate =>  Initial_Crate,
                      Final_Crate   =>+ Initial_Crate);

   procedure Weapon_Smuggling (Initial_Crate : in out Fruit_Crate;
                               Final_Crate   : in out Fruit_And_Weapons_Crate)
   is
      package Weapons_In_Fake_Watermellons is
        new Internal_Generic (New_Item_T      => Fruits_And_Weapons,
                              New_Inventory_T => Fruit_And_Weapons_Crate,
                              Equivalent      => Fruits_To_Fruits_And_Weapons);
      use Weapons_In_Fake_Watermellons;
   begin
      Fill_Empty_Slots (Initial_Crate, Fake_Watermellon);
      Replace_Items (Initial_Crate, Final_Crate, Grenade);
   end Weapon_Smuggling;
end Test;
