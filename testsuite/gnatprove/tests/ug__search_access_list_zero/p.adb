with Loop_Types; use Loop_Types;

package body P with
  SPARK_Mode
is
   function Search_List_Zero (L : access List_Cell) return access List_Cell is
      B : access List_Cell := L;
   begin
      while B /= null and then B.Value /= 0 loop
         pragma Loop_Invariant
           (For_All_List (L, Is_Non_Zero'Access) =
                For_All_List (B, Is_Non_Zero'Access));
         B := B.Next;
      end loop;

      return B;
   end Search_List_Zero;
end P;
