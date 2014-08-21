package body Ineffective_Constant
  with Refined_State => (State => G)
is
   type Record_T is record
      X : Integer;
   end record;

   G : Integer := 0;
   C : constant Record_T := Record_T'(X => 0);

   procedure P
     with Refined_Global => G
   is
   begin
      pragma Assert (C.X + G = 0);
   end P;
end Ineffective_Constant;

