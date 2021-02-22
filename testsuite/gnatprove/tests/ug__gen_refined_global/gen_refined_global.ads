package Gen_Refined_Global with
  SPARK_Mode,
  Abstract_State => State
is
   procedure Set_Global with
     Global => (Output => State);

   procedure Set_Global_Twice with
     Global => (Output => State);

   procedure Set_Global_Conditionally (X : Boolean) with
     Global  => (Output => State),
     Depends => (State => X);

end Gen_Refined_Global;
