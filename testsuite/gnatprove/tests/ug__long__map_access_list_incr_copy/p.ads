with Loop_Types; use Loop_Types;

package P with
  SPARK_Mode
is
   function Small_Enough (X : Component_T) return Boolean is
     (X /= Component_T'Last);

   function Equal (X, Y : Component_T) return Boolean is (X = Y);

   function Is_Incr (X, Y : Component_T) return Boolean is
     (X < Y and then Y = X + 1);

   function Copy (L : access List_Cell) return List_Acc with
     Ghost,
     Import,
     Post => For_All_List (L, Copy'Result, Equal'Access);

   procedure Map_List_Incr (L : access List_Cell) with
     Pre  => For_All_List (L, Small_Enough'Access),
     Post => For_All_List (Copy (L)'Old, L, Is_Incr'Access);
end P;
