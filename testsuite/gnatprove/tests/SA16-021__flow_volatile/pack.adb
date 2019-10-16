package body Pack with
  SPARK_Mode,
  Refined_State => (Var => V)
is
   V : Integer with Volatile, Async_Readers;

   procedure Direct_Write is
   begin
      V := 0;
      V := 1;
   end;

   procedure Indirect_Write is
   begin
      Direct_Write;
      Direct_Write;
   end;

   procedure Mixed_Write is
   begin
      Direct_Write;
      V := 0;
   end;

end Pack;
