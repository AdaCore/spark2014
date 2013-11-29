package body Outer
  with SPARK_Mode,
       Refined_State => (State => Inner.Var)
is
   package Inner
     with Initializes => (Var => Init.Var)
   is
      Var : Integer := Init.Var;
   end Inner;
end Outer;
