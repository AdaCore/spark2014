package body Callers_Caller is
   function Add3 (R : Pr_Record_TTT) return Integer is
      (Add2 (Pr_Record_TT (R)));

   procedure Test2 is
      R : Pr_Record_TTT;
   begin
      pragma Assert (Add3 (R) = 0);
   end Test2;
end Callers_Caller;
