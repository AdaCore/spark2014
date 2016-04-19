package Use_Ghost2 with SPARK_Mode is

   G_Var : Integer with Ghost;

   procedure Do_Stuff (Success : out Boolean) with
     Import,
     Global => (Proof_In => G_Var),
     Post => Success = (G_Var = G_Var'Old);

   procedure Main (X : out Integer);

end Use_Ghost2;
