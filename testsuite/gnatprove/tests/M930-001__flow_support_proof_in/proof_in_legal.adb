package body Proof_In_Legal
  with SPARK_Mode,
       Refined_State => (State => Body_Var)
is
   Body_Var : Integer := 1;

   function Is_OK_To_Increase return Boolean is
     (Body_Var > 0)
     with Refined_Global => Body_Var;

   procedure Increase (X : in out Integer)
     with Refined_Global  => (Proof_In => (Body_Var,
                                           Var))
   is
   begin
      pragma Assert (Var = 0);  --  Just a random assertion...

      X := X + 1;
   end Increase;
end Proof_In_Legal;
