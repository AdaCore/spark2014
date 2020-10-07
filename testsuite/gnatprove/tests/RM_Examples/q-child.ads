   private package Q.Child
     with Abstract_State => (C1 with Part_Of => Q.Q1)
   is
      --  C1 rather than the encapsulating state abstraction
      --  may be used in aspect specifications provided
      --  Q.Q1 is not also denoted in the same aspect
      --  specification.

      --  Here C1 is used so Q1 cannot also be used in
      --  the aspect specifications of this subprogram.
      procedure Init_Q1
        with Global  => (Output => C1),
             Depends => (C1 => null);

      --  Q.Hidden_State which is a constituent of Q.Q2
      --  is visible here so it can be used in a aspect
      --  specification provided Q.Q2 is not also used.
      procedure Init_Q2
         with Global  => (Output => Q.Hidden_State),
              Depends => (Q.Hidden_State => null);
   end Q.Child;
