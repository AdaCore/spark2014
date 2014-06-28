with Ada.Containers.Formal_Ordered_Maps;
use Ada.Containers;

package Replacement with
  SPARK_Mode
is

   function Lt_Integer (Left, Right : Integer) return Boolean is (Left < Right);
   function Eq_Integer (Left, Right : Integer) return Boolean is (Left = Right);
   package Inverse_Sets is new
     Formal_Ordered_Maps (Key_Type     => Integer,
                          Element_Type => Integer,
                          "<"          => Lt_Integer,
                          "="          => Eq_Integer);
   subtype Inverse_Set is Inverse_Sets.Map;
   use Inverse_Sets;

   procedure Refine (D : in out Inverse_Set; K : Integer) with
     Pre => Contains (D, K);

end Replacement;
