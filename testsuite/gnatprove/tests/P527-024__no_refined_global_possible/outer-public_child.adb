package body Outer.Public_Child is
   --  Outer.Hidden is visible here but the refinement of A2 is not so there is
   --  no Refined_Global.
   procedure Init_A2_With (Val : in Integer)
--     with Refined_Global => (Output => Outer.A2)
   is
   begin
      Outer.Init_A2;
      Outer.Private_State := Val;
   end Init_A2_With;
end Outer.Public_Child;
