   package body Q.Child
     with Refined_State => (C1 => Actual_State)
   is
      --  C1 shall not be denoted here - only Actual_State
      --  but Q.Q2 and Q.Hidden_State may be denoted.
      Actual_State : Integer;

      procedure Init_Q1
        with Refined_Global  => (Output => Actual_State),
             Refined_Depends => (Actual_State => null)
      is
      begin
         Actual_State := 0;
      end Init_Q1;

      --  The refinement of Q2 is not visible and so Init_Q2
      --  has no Refined_Global or Refined_Depends aspects.
      procedure Init_Q2 is
      begin
         Q.Hidden_State := 0;
      end Init_Q2;

   end Q.Child;
