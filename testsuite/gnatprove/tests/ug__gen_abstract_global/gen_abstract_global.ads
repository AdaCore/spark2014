package Gen_Abstract_Global with
  SPARK_Mode,
  Abstract_State => State
is
   procedure Set_Global;

   procedure Set_Global_Twice;

   procedure Set_Global_Conditionally (X : Boolean) with
     Global  => (Output => State),
     Depends => (State => X);

end Gen_Abstract_Global;
