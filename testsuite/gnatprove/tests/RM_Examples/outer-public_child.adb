   package body Outer.Public_Child is
      --  Outer.Hidden is visible here but the
      --  refinement of A2 is not so there are
      --  no Refined_Global or Refined_Depends.
      procedure Init_A2_With (Val : in Integer) is
      begin
         Outer.Init_A2;
         Outer.Hidden_State := Val;
      end Init_A2_With;
   end Outer.Public_Child;
