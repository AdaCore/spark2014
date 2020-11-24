   with Q.Child;

   package body Q
     with Refined_State => (Q1 => Q.Child.C1,
                            Q2 => (Hidden_State, State_In_Body))
   is
      --  Q1 and Q2 shall not be denoted here but the constituents
      --  Q.Child.C1, State_In_Body and Hidden_State may be.
      State_In_Body : Integer;

      procedure Init_Q1
        with Refined_Global  => (Output => Q.Child.C1),
             Refined_Depends => (Q.Child.C1 => null)
      is
      begin
         Q.Child.Init_Q1;
      end Init_Q1;

      procedure Init_Q2
        with Refined_Global  => (Output => (Hidden_State, State_in_Body)),
             Refined_Depends => ((Hidden_State, State_in_Body) => null)
      is
      begin
         State_In_Body := 42;
         Q.Child.Init_Q2;
      end Init_Q2;
   end Q;
