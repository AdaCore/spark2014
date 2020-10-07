   package Q
     with Abstract_State => (Q1, Q2)
   is
      --  Q1 and Q2 may be denoted here
      procedure Init_Q1
        with Global  => (Output => Q1),
             Depends => (Q1 => null);

      procedure Init_Q2
        with Global  => (Output => Q2),
             Depends => (Q2 => null);

   private
      Hidden_State : Integer
        with Part_Of => Q2;
   end Q;
