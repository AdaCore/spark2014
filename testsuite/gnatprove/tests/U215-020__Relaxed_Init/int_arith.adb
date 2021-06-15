package body Int_Arith is
   procedure Lemma_Sum_Ones (A : Data; I : Index)
   with
     Ghost,
     Pre  => I in A'Range
       and then (for all J in 1 .. I => A(J)'Initialized)
       and then (for all J in 1 .. I => A(J) = 1),
     Post => Sum (A, Up_To => I) = I
   is
   begin
      for J in 1 .. I loop
         pragma Loop_Invariant (Sum (A, J) = J);
      end loop;
   end Lemma_Sum_Ones;

   procedure Init_SPARK (A : in out Data; S : Natural) is
   begin
      for I in 1 .. S loop
         A(I) := 1;
         pragma Loop_Invariant (for all J in 1 .. I => A(J) = 1);
      end loop;
      if S > 0 then
         Lemma_Sum_Ones (A, S);
      end if;
   end Init_SPARK;
end Int_Arith;
