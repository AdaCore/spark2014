package body Proof_In_Illegal
  with SPARK_Mode,
       Refined_State => (State => Body_Var)
is
   Body_Var : Integer;

   function Error_Derived_From_Proof_In (X : Integer) return Integer
     with Refined_Global => (Proof_In => (Body_Var,
                                          Var))
   is
      Temp : Integer;
   begin
      Temp := X + Body_Var;
      Temp := Temp + Var;
      return Temp;  --  Error, derived output from Proof_In.
   end Error_Derived_From_Proof_In;

   function Warning_Proof_In_Not_Used (X : Integer) return Integer is
     (X)  --  Warning, Proof_In never used.
     with Refined_Global => (Proof_In => (Body_Var,
                                          Var));
end Proof_In_Illegal;
