package body Gen_State with SPARK_Mode, Refined_State => (State => Error) is
   procedure Run with
     Refined_Global  => (Output => Error),
     Refined_Depends => (Error => null)
   is
   begin
      Error := True;
   end Run;
end Gen_State;
