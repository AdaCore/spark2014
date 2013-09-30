package Ghost_Illegal_1
  with SPARK_Mode
is
   --  TU: 4. Only functions can be explicitly declared with the Convention
   --  aspect Ghost. [This means that the scope of the following rules is
   --  restricted to functions, even though they are stated in more general
   --  terms.]
   Ghost_Var : Integer
     with Convention => Ghost;

   --  TU: 4. Only functions can be explicitly declared with the Convention
   --  aspect Ghost. [This means that the scope of the following rules is
   --  restricted to functions, even though they are stated in more general
   --  terms.]
   procedure Ghost_Proc
     with Convention => Ghost;

   procedure P1
     with Global => (Output => Ghost_Var);
end Ghost_Illegal_1;