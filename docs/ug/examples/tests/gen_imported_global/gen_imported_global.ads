package Gen_Imported_Global with
  SPARK_Mode,
  Abstract_State => (State with External =>
                        (Async_Writers,
                         Async_Readers => False,
                         Effective_Reads => False,
                         Effective_Writes => False))
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
