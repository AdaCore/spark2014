with Loop_Types; use Loop_Types;

package body P with
  SPARK_Mode
is
   procedure Map_List_Incr (L : access List_Cell) is
      B : access List_Cell := L;
   begin
      while B /= null loop
         pragma Loop_Invariant (For_All_List (B, Small_Enough'Access));
         pragma Loop_Invariant
           (if For_All_List (At_End (B), Bigger_Than_First'Access)
            then For_All_List (At_End (L), Bigger_Than_First'Access));
         B.Value := B.Value + 1;
         B := B.Next;
      end loop;
   end Map_List_Incr;
end P;
