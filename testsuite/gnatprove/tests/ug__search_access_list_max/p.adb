with Loop_Types; use Loop_Types;
with SPARK.Big_Integers; use SPARK.Big_Integers;

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
         pragma Loop_Variant (Decreases => Length (B));
         declare
            Prec : access List_Cell := B;
            Max  : constant Component_T := B.Value;
         begin
            loop
               B := B.Next;
               exit when B = null or else B.Value > Max;
               pragma Loop_Invariant (B /= null);
               pragma Loop_Invariant (B.Value <= Max);
               pragma Loop_Invariant (Length (B) < Length (B)'Loop_Entry);
               pragma Loop_Invariant
                 (for all M in Max .. Component_T'Last =>
                    (if All_Smaller_Than_Max (B, M)
                     then All_Smaller_Than_Max (L, M)));
               pragma Loop_Variant (Decreases => Length (B));
            end loop;
            if B = null then
               return Prec;
            end if;
         end;
      end loop;
   end Search_List_Max;
end P;
