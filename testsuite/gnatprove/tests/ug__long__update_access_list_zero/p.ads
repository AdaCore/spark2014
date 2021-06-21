with Loop_Types; use Loop_Types;

package P with
  SPARK_Mode
is
   function Equal (X, Y : Component_T) return Boolean is (X = Y);

   function Copy (L : access List_Cell) return List_Acc with
     Ghost,
     Import,
     Post => For_All_List (L, Copy'Result, Equal'Access);

   function Updated_If_Less_Than_Threshold
     (L1, L2    : access constant List_Cell;
      Threshold : Component_T) return Boolean
   is
     ((L1 = null) = (L2 = null)
      and then
        (if L1 /= null then
             (if L1.Value <= Threshold then L2.Value = 0
              else L2.Value = L1.Value)
         and then Updated_If_Less_Than_Threshold (L1.Next, L2.Next, Threshold)))
   with Annotate => (GNATprove, Terminating);
   pragma Annotate (GNATprove, False_Positive, "is recursive",
                    "The recursive call occurs on a strictly smaller lists");

   procedure Update_List_Zero (L : access List_Cell; Threshold : Component_T) with
     Post => Updated_If_Less_Than_Threshold (Copy (L)'Old, L, Threshold);
end P;
