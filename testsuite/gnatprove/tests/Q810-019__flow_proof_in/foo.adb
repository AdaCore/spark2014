package body Foo
with
   SPARK_Mode => On,
   Refined_State => (State => Global_Var)
is

   Global_Var : Natural := 0;

   procedure Do_Process (Val : Natural)
   with
      Global => (Output   => Global_Var,
                 Proof_In => Bar.ID),
      Pre    => Bar.ID = 5;

   -------------------------------------------------------------------------

   procedure Do_Process (Val : Natural)
   is
   begin
      Global_Var := Val;
   end Do_Process;

   -------------------------------------------------------------------------

   procedure Process (Value : Natural)
--   with
--      Refined_Global => (Output => Global_Var, Proof_In => Bar.Id)
--   this contract makes the code accepted by both 17.2 and later
   is
   begin
      Do_Process (Val => Value);
   end Process;

end Foo;
