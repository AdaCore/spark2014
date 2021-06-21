with Loop_Types; use Loop_Types;

package body P with
  SPARK_Mode
is
   procedure Init_List_Zero (L : access List_Cell) is
      B : access List_Cell := L;
   begin
      while B /= null loop
         pragma Loop_Invariant
           (if For_All_List (At_End (B), Is_Zero'Access)
            then For_All_List (At_End (L), Is_Zero'Access));
         B.Value := 0;
         B := B.Next;
      end loop;
   end Init_List_Zero;
end P;
