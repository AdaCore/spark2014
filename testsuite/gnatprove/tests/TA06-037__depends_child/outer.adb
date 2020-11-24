package body Outer
  with Refined_State => (A1 => Inner.B1,
                         A2 => (Hidden_State, State_In_Body))
  --  A1 and A2 cannot be denoted in the body of Outer because their
  --  refinements are visible.
is
   State_In_Body : Integer;

   package body Inner
     with Refined_State => (B1 => null)  --  Oh, there isn't any state after all
   is
      procedure Init_B1
        with Refined_Global  => null,  --  Refined_Global and
             Refined_Depends => null   --  Refined_Depends of a null refinement
      is
      begin
         null;
      end Init_B1;

      procedure Init_A2
        --  The Global sparct is already in terms of the constituent
        --  Hidden_State which is part of A2, so no refined
        --  Global or Depends aspects are required.
      is
      begin
         Outer.Hidden_State := 0;
      end Init_A2;

   end Inner;

   procedure Init_A1
     with Refined_Global  => (Output => Inner.B1),
          Refined_Depends => (Inner.B1 => null)
   is
   begin
      Inner.Init_B1;
   end Init_A1;

   procedure Init_A2
     with Refined_Global  => (Output => (Hidden_State, State_In_Body)),
          Refined_Depends => ((Hidden_State, State_In_Body) => null)
   is
   begin
      State_In_Body := 42;
      Inner.Init_A2;
   end Init_A2;

end Outer;
