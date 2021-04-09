with Loop_Types; use Loop_Types;

package body P with
  SPARK_Mode
is
   procedure Map_List_Incr (L : access List_Cell) is
      L_Old : constant List_Acc := Copy (L) with Ghost;
      pragma Annotate (GNATprove, Intentional, "memory leak might occur",
                       "The code will be compiled with assertions disabled");
      B     : access List_Cell := L;
      B_Old : access constant List_Cell := L_Old with Ghost;
   begin
      while B /= null loop
         pragma Loop_Invariant (For_All_List (B, Small_Enough'Access));
         pragma Loop_Invariant (For_All_List (B, B_Old, Equal'Access));
         pragma Loop_Invariant
           (if For_All_List (B_Old, At_End (B), Is_Incr'Access)
            then For_All_List (L_Old, At_End (L), Is_Incr'Access));
         B.Value := B.Value + 1;
         B := B.Next;
         B_Old := B_Old.Next;
      end loop;
      pragma Assert
        (For_All_List (L_Old, At_End (L), Is_Incr'Access));
   end Map_List_Incr;
end P;
