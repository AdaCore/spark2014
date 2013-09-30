package body Assume_And_Assert_And_Cut_Illegal is
   procedure Prover_Forgets_After_Assert_And_Cut is
   --  TU: 1. Pragma Assert_And_Cut is the same as a pragma Assert except it
   --  also acts as a cut point in formal verification. The cut point means
   --  that a prover is free to forget all information about modified variables
   --  that has been established from the statement list before the cut point.
   --  Only the given Boolean expression is carried forward.
      X, Y : Integer;
   begin
      X := 0;
      Y := 0;
      pragma Assert_And_Cut (X = 0);
      pragma Assert (Y = 0);  --  This cannot be proven
      null;
   end Prover_Forgets_After_Assert_And_Cut;
end Assume_And_Assert_And_Cut_Illegal;