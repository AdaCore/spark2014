   package Outer.Public_Child is
      --  Outer.A1 and Outer.A2 are visible but
      --  Outer.Hidden_State is not (by the rules of Ada).
      --  The Global and Depends Aspects are in terms
      --  of the encapsulating state abstraction Outer.A2.
      procedure Init_A2_With (Val : in Integer)
        with Global  => (Output => Outer.A2),
             Depends => (Outer.A2 => Val);
   end Outer.Public_Child;
