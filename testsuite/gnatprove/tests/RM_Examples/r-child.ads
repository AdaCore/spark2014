   private package R.Child
     with Abstract_State => (R2 with Part_Of => R.R1)
   is
      --  Both R.R1 and R2 are visible.

      --  Here more than just the R2 constituent of R.R1
      --  will be updated and so we use R.R1 in the
      --  aspect specifications rather than R2.
      --  R2 cannot also be used in the aspect
      --  specifications of this subprogram.
      procedure Private_Op (I, J : in Integer)
        with Global  => (In_Out => R.R1),
             Depends => (R.R1 =>+ (I, J));
   end R.Child;
