package body Pack is
   procedure Prove_Sum_Eq (A, B : My_Arr) with
     Ghost,
     Pre  => A = B,
     Post => Sum (A) = Sum (B)
   is
   begin
      if A'Length = 0 then
         return;
      end if;
      Prove_Sum_Eq (A (A'First .. A'Last - 1), B (B'First .. B'Last - 1));
   end Prove_Sum_Eq;

   procedure truncate (M : in out My_Arr; S : Natural)
   is
      CS  : Natural := 0;
      O_M : My_Arr := M with Ghost;
   begin
      for I in M'Range loop
         if CS + M (I) > S then
            M (I) := S - CS;
         end if;
         CS := CS + M (I);
         Prove_Sum_Eq (M (M'First .. I - 1), O_M (M'First .. I - 1));
         pragma Loop_Invariant (CS = Sum (M (M'First .. I)));
         pragma Loop_Invariant (S >= CS);
         O_M := M;
      end loop;
   end truncate;
end Pack;
