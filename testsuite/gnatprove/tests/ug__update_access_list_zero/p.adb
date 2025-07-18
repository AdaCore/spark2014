with Loop_Types; use Loop_Types;

package body P with
  SPARK_Mode
is
   procedure Update_List_Zero (L : access List_Cell; Threshold : Component_T) is
      L_Old : constant List_Acc := Copy (L) with Ghost;
      pragma Annotate (GNATprove, Intentional, "memory leak might occur",
                       "The code will be compiled with assertions disabled");
      B     : access List_Cell := L;
      B_Old : access constant List_Cell := L_Old with Ghost;
   begin
      while B /= null loop
         pragma Loop_Invariant (For_All_List (B, B_Old, Equal'Access));
         pragma Loop_Invariant
           (if Updated_If_Less_Than_Threshold (B_Old, At_End (B), Threshold)
            then Updated_If_Less_Than_Threshold (L_Old, At_End (L), Threshold));
         if B.Value <= Threshold then
            B.Value := 0;
         end if;
         B := B.Next;
         B_Old := B_Old.Next;
      end loop;
      pragma Assert
        (Updated_If_Less_Than_Threshold (L_Old, At_End (L), Threshold));
   end Update_List_Zero;
end P;
