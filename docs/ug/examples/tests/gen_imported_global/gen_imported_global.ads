package Gen_Imported_Global with
  SPARK_Mode,
  Abstract_State => State
is
   procedure Set_Global with
     Import,
     Convention => C,
     Global => (Output => State);

   procedure Set_Global_Twice;

   procedure Set_Global_Conditionally (X : Boolean) with
     Global  => (Output => State),
     Depends => (State => X);

end Gen_Imported_Global;
