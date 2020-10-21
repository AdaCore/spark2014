package Functions with Annotate => (GNATprove, Terminating) is

   function Non_Ter_Func return Boolean
     with Post => Non_Ter_Func'Result = True;

   function Expr_Func return Boolean is (Non_Ter_Func);

   package Nested with Annotate => (GNATprove, Terminating) is
      procedure Nested_Proc;
   end Nested;

end Functions;
