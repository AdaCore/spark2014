with Loop_Types; use Loop_Types;

package P with
  SPARK_Mode
is
   function Is_Zero (X : Component_T) return Boolean is
     (X = 0);

   procedure Init_List_Zero (L : access List_Cell) with
     Post => For_All_List (L, Is_Zero'Access);
end P;
