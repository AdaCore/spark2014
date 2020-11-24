   package R
     with Abstract_State => R1
   is
      -- R1 may be denoted here
      procedure Init_R1
        with Global  => (Output => R1),
             Depends => (R1 => null);

      procedure Op_1 (I : in Integer)
        with Global  => (In_Out => R1),
             Depends => (R1 =>+ I);
   end R;
