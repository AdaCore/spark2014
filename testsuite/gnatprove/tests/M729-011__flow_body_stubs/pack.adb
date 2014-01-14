package body Pack
  with SPARK_Mode,
       Refined_State => (State => (A, B))
is
   A, B : Integer;

   procedure Initialize_State is separate
     with Refined_Global => (Output => (A, B));

   procedure Double_B is separate
     with Global => (In_Out => B);--  ,
          --  Pre    => B = Var;
begin
   Initialize_State;
   Double_B;
end Pack;
