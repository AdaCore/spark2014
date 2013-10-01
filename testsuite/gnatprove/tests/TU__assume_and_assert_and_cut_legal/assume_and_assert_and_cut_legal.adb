package body Assume_And_Assert_And_Cut_Legal is
   procedure Assume_Creates_No_Proof_Obligation (Par  : in     Integer;
                                                 Par2 :    out Integer)
     --  TU: 2. Pragma Assume is the same as a pragma Assert except that there
     --  is no proof obligation to prove the truth of the Boolean expression
     --  that is its actual parameter. [Pragma Assume indicates to proof tools
     --  that the expression can be assumed to be True.]
     with Post => (Par2 >= 10)
   is
   begin
      pragma Assume (Par >= 5 and Par <= 1000);
      Par2 := 2 * Par;
   end Assume_Creates_No_Proof_Obligation;
end Assume_And_Assert_And_Cut_Legal;