with Loop_Types; use Loop_Types;

package P with
  SPARK_Mode
is
   function Is_Non_Zero (X : Component_T) return Boolean is
     (X /= 0);

   function Search_List_Zero (L : access List_Cell) return access List_Cell with
     Post =>
       ((Search_List_Zero'Result = null) = For_All_List (L, Is_Non_Zero'Access)
        and then
            (if Search_List_Zero'Result /= null then Search_List_Zero'Result.Value = 0));
end P;
