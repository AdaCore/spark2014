with Loop_Types; use Loop_Types;

package P with
  SPARK_Mode
is
   function Small_Enough (X : Component_T) return Boolean is
     (X /= Component_T'Last);
   function Bigger_Than_First (X : Component_T) return Boolean is
     (X /= Component_T'First);

   procedure Map_List_Incr (L : access List_Cell) with
     Pre  => For_All_List (L, Small_Enough'Access),
     Post => For_All_List (L, Bigger_Than_First'Access);
end P;
