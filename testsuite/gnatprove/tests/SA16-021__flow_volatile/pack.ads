package Pack with
  SPARK_Mode,
  Abstract_State => (Var with External => Async_Readers)
is
   procedure Direct_Write with
     Global => (Output => Var);

   procedure Indirect_Write with
     Global => (Output => Var);

   procedure Mixed_Write with
     Global => (Output => Var);
end Pack;
