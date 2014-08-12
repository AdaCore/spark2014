package body Caller is
   function Add2 (R : Pr_Record_TT) return Integer is (Add (Pr_Record_T (R)));

   procedure Test is
      I : Pr_TT;
      R : Pr_Record_TT;
   begin
      pragma Assert (Evaluate (Pr_T (I)) = 0);
      pragma Assert (Add2 (R) = 0);
   end Test;
end Caller;

