with Higher_Order;
package Test_Higher_Order with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   subtype Small_Enough is Nat_Array with
     Predicate => (for all I in Small_Enough'Range =>
                     Small_Enough (I) < Integer'Last);

   function Add_One (X : Integer) return Integer is (X + 1) with
     Pre => X < Integer'Last;

   function Add_All is new Higher_Order.Map_F
     (Index_Type => Positive,
      Element_1  => Natural,
      Array_1    => Small_Enough,
      Element_2  => Natural,
      Array_2    => Nat_Array,
      F          => Add_One);

   function A_Small_Enough (X : Integer) return Boolean is
     (X < Integer'Last);

   procedure Add_All is new Higher_Order.Proc_Map_F
     (Index_Type => Positive,
      Element    => Natural,
      Array_Type => Nat_Array,
      Init_Prop  => A_Small_Enough,
      F          => Add_One);

   subtype Small_Int is Integer range - 100 .. 100;

   subtype Small_Index is Positive range 1 .. 100;

   type Small_Int_Array is array (Small_Index range <>) of Small_Int;

   function In_Range (A : Small_Int_Array; X : Integer; C : Natural)
                      return Boolean
   is (X in Integer'First + 100 * (A'Length - C) .. Integer'Last - 100 * (A'Length - C))
     with Pre => C <= A'Length;

   package Sum is new Higher_Order.Fold
     (Index_Type => Small_Index,
      Element_1  => Small_Int,
      Array_Type => Small_Int_Array,
      Element_2  => Integer,
      Ind_Prop   => In_Range,
      F          => "+");

   subtype Small_Nat is Natural range 0 .. 100;
   type Matrix is array (Small_Index, Small_Index) of Small_Nat;

   function In_Range (A : Matrix; X : Integer; C1, C2 : Natural)
                      return Boolean
   is (X <= Integer'Last - 100 * (A'Length (1) - C1) * A'Length (2) - 100 * (A'Length (2) - C2))
     with Pre => C1 <= A'Length (2) and C2 <= A'Length (1);

   package Sum_2 is new Higher_Order.Fold_2
     (Index_1    => Small_Index,
      Index_2    => Small_Index,
      Element_1  => Small_Nat,
      Array_Type => Matrix,
      Element_2  => Integer,
      Ind_Prop   => In_Range,
      F          => "+");

end Test_Higher_Order;
