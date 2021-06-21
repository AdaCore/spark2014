with Loop_Types; use Loop_Types;

package body P with
  SPARK_Mode
is
   procedure Validate_List_Zero
     (L       : access constant List_Cell;
      Success : out Boolean)
   is
      C : access constant List_Cell := L;
   begin
      while C /= null loop
         pragma Loop_Invariant
           (For_All_List (L, Is_Zero'Access) = For_All_List (C, Is_Zero'Access));
         if C.Value /= 0 then
            Success := False;
            return;
         end if;
         C := C.Next;
      end loop;

      Success := True;
   end Validate_List_Zero;
end P;
