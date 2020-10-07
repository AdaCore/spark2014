   package body R.Child
     with Refined_State => (R2 => Actual_State)
   is
      --  R2 shall not be denoted here - only Actual_State
      --  but R.R1 may be denoted.
      Actual_State : Integer;

      --  The Global and Depends aspects of Private_Op
      --  are in terms of R.R1 and the refinement of
      --  R.R1 is not visible and so Refined_Global
      --  and Refined_Depends are not required.
      procedure Private_Op (I, J : in Integer) is
      begin
         R.Op_1 (I);
         Actual_State := J;
      end Private_Op;
   end R.Child;
