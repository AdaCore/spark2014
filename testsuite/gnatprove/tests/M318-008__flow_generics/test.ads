package Test is
   --  Generic subprograms

   --  Exchange  --

   generic
      type Elem is private;
   procedure Exchange (U, V : in out Elem)
      with Depends => (U => V,
                       V => U);

   --  Generic packages

   --  On_Vectors  --

   generic
      type Item   is private;
      type Vector is array (Positive range <>) of Item;
      with function Sum (X, Y : Item) return Item;
   package On_Vectors is
      procedure Sum (A, B : Vector; C : in out Vector)
         with Depends => (C =>+ (A, B)),
              Pre => A'First = C'First and
                     A'Last  = C'Last  and
                     A'Length = B'Length;
   end On_Vectors;

   --  On_Records  --

   generic
      type Item is private;
   package On_Records is
      type Array_Of_Items_T is array (1 .. 5) of Item;

      type Record_T (D : Natural := 0) is
         record
            case D is
               when 1 =>
                  Single_Item : Item;
               when 2 =>
                  A, B : Item;
               when others =>
                  Arr : Array_Of_Items_T;
            end case;
         end record;

      procedure Copy_One_Item (Rec1 : in Record_T; Rec2 : in out Record_T)
         with Depends =>  (Rec2 =>+ Rec1),
              Pre     =>  Rec1.D = Rec2.D;
   end On_Records;
end Test;
