package Outer.Public_Child is
   --  Outer.A2 is visible but Outer.Hidden_State is not (by the rules of Ada).
   --  The Global aspect is in terms of the encapsulating state abstraction
   --  Outer.A2.
   procedure Init_A2_With (Val : in Integer)
     with Global => (Output => Outer.A2);
end Outer.Public_Child;
