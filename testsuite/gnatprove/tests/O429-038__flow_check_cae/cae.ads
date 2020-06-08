package CAE
  with Abstract_State => State
is
   Var : Integer := 1
     with Constant_After_Elaboration;

   procedure P with Global => (Output => Var);   --  Problem

   procedure P2;  --  Problem

   procedure P3;  -- OK
private
   Priv_Var : Integer := 2
     with Part_Of => State,
          Constant_After_Elaboration => True;

   procedure P4;  -- Problem
end CAE;
