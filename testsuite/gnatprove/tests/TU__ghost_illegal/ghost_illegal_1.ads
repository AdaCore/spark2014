package Ghost_Illegal_1
  with SPARK_Mode
is
   Ghost_Var : Integer
     with Convention => Ghost;

   procedure Ghost_Proc
     with Convention => Ghost;

   procedure P1
     with Global => (Output => Ghost_Var);
end Ghost_Illegal_1;
