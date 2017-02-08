with Ada.Containers.Formal_Ordered_Maps;
use Ada.Containers;

package Replacement with
  SPARK_Mode
is
   type Set is array (Integer range <>) of Integer;

   package Inverse_Sets is new
     Formal_Ordered_Maps (Key_Type     => Integer,
                          Element_Type => Integer);
   subtype Inverse_Set is Inverse_Sets.Map;
   use Inverse_Sets;

   procedure Refine (A : Set; D : in out Inverse_Set; K : Integer) with
     Pre => Contains (D, K) and then
            (for all C in D => A (Element (D, C)) = Key (D, C));

end Replacement;
