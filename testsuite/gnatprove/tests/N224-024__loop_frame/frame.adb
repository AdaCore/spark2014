package body Frame is

   procedure Threshold_Ar (A : in out Ar) is
   begin
      for J in Index loop
         if A(J) > 10 then
            A(J) := 10;
         end if;
         pragma Loop_Invariant
           (for all K in 1 .. J => A(K) =
              (if A'Loop_Entry(K) > 10 then 10 else A'Loop_Entry(K)));
      end loop;
   end Threshold_Ar;

   procedure Copy_Rec (A : in out Arrec) is
   begin
      for J in Index loop
         A(J).C1 := A(J).C2;
         pragma Loop_Invariant
           (for all K in 1 .. J => A(K).C1 = A'Loop_Entry(K).C2);
      end loop;
   end Copy_Rec;

end Frame;
