with Loop_Types; use Loop_Types;

package body P with
  SPARK_Mode
is
   function Search_List_Max
     (L : not null access List_Cell) return not null access List_Cell
   is
      B : access List_Cell := L;
   begin
      loop
         pragma Loop_Invariant (B /= null);
         pragma Loop_Invariant
           (for all M in B.Value .. Component_T'Last =>
              (if All_Smaller_Than_Max (B, M)
               then All_Smaller_Than_Max (L, M)));
         declare
            Prec : access List_Cell := B;
            Max  : constant Component_T := B.Value;
         begin
            while B /= null and then B.Value <= Max loop
               pragma Loop_Invariant
                 (for all M in Max .. Component_T'Last =>
                    (if All_Smaller_Than_Max (B, M)
                     then All_Smaller_Than_Max (L, M)));
               B := B.Next;
            end loop;
            if B = null then
               return Prec;
            end if;
         end;
      end loop;
   end Search_List_Max;
end P;
