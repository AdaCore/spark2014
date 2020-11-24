   package Outer
     with Abstract_State => (A1, A2)
   is
      procedure Init_A1
        with Global  => (Output => A1),
             Depends => (A1 => null);

      procedure Init_A2
        with Global  => (Output => A2),
             Depends => (A2 => null);

   private
      --  A variable declared in the private part must have a Part_Of aspect
      Hidden_State : Integer
        with Part_Of => A2;

      package Inner
        with Abstract_state => (B1 with Part_Of => Outer.A1)
        --  State abstraction declared in the private
        --  part must have a Part_Of option.
      is
         --  B1 may be used in aspect specifications provided
         --  Outer.A1 is not also used.
         procedure Init_B1
           with Global  => (Output => B1),
                Depends => (B1 => null);

         procedure Init_A2
           --  We can only refer to Outer.Hidden_State which is a constituent
           --  of Outer.A2 if the subprogram does not also refer to Outer.A2.
           with Global  => (Output => Hidden_State),
                Depends => (Hidden_State => null);
      end Inner;
   end Outer;
