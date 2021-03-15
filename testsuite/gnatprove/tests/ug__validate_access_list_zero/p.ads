with Loop_Types; use Loop_Types;

package P with
  SPARK_Mode
is
   function Is_Zero (X : Component_T) return Boolean is
     (X = 0);

   procedure Validate_List_Zero
     (L       : access constant List_Cell;
      Success : out Boolean)
   with
     Post => Success = For_All_List (L, Is_Zero'Access);
end P;
