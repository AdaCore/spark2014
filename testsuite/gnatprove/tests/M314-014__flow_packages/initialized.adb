package body Initialized
  with SPARK_Mode,
       Refined_State => (State => Var)
is
   Var : Natural;

   function Get return Natural is
      (Var)
      with Refined_Global => Var;

begin
   Var := 0;
end Initialized;
