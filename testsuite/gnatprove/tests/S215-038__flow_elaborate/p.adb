package body P
  with Refined_State => (State => Hidden_Var)
is
   Hidden_Var : Integer := 10;

   function Read_From_State return Integer is (Hidden_Var);
end P;
