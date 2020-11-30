package P
  with Abstract_State => State
is
   function F return Boolean with Global => State;

   generic
   package Nested_Generic_Package
     with Abstract_State => State_Gen_Pkg,
          Initial_Condition => F
   is
      procedure Nested_Proc (X : in out Integer);
   end;
private
   A : Integer with Part_Of => State;
end P;
