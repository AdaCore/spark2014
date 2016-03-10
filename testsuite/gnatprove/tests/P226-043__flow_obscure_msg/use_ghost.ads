package Use_Ghost with SPARK_Mode is

   G_Var : Integer with Ghost;

   procedure Do_Stuff (Success : out Boolean) with
     Import,
     Global => (Input => G_Var),
     Post => Success = (G_Var = G_Var'Old);

   procedure Main (X : out Integer);

end Use_Ghost;
