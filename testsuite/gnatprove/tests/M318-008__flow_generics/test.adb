package body Test is
   ----------------
   --  Exchange  --
   ----------------

   procedure Exchange (U, V : in out Elem)
   is
      Temp : Elem;
   begin
      Temp := U;
      U    := V;
      V    := Temp;
   end Exchange;

   procedure Swap is new Exchange (Elem => Integer);
   procedure Swap is new Exchange (Character);

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
      procedure Sum (A, B : Vector; C : in out Vector)
      is
      begin
         for I in A'Range loop
            C (I) := Sum (A (I), B (I + B'First - A'First));
         end loop;
      end Sum;
   end On_Vectors;

   type Table is array (Positive range <>) of Integer;

   package Int_Vectors is new On_Vectors(Integer, Table, "+");

   procedure Sum_And_Reverse (A, B : in Table ; C : in out Table)
      with Depends => (C =>+ (A, B)),
           Pre => A'First = C'First and
                  A'Last  = C'Last  and
                  A'Length = B'Length;

   procedure Sum_And_Reverse (A, B : in Table; C : in out Table)
   is
   begin
      Int_Vectors.Sum (A, B, C);
      for I in C'First .. C'Last / 2 loop
         Swap (C (I), C (C'Last - I + C'First));
      end loop;
   end Sum_And_Reverse;

   ------------------
   --  On_Records  --
   ------------------

   package body On_Records is
      procedure Copy_One_Item (Rec1 : in Record_T; Rec2 : in out Record_T)
      is
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

   type Fruits is (Apple, Orange, Banana, Strawberry, Grapes, Pineapple);

   package Fruit_Rec is new On_Records (Item => Fruits);
   use Fruit_Rec;

   procedure Replace_A_Fruit (Rec1 : in Record_T; Rec2 : in out Record_T) renames
     Copy_One_Item;

   Apple_Basket : Record_T (0) := (D => 0, Arr => (Apple, Apple, Apple, Apple, Apple));
   Mixed_Basket : Record_T := (D => 0, Arr => (Banana, Strawberry, Orange, Grapes, Pineapple));

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
end Test;
