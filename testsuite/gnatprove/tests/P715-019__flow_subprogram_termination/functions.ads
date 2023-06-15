package Functions with Always_Terminates is

   function Non_Ter_Func return Boolean
     with Post => Non_Ter_Func'Result = True;

   function Expr_Func return Boolean is (Non_Ter_Func);

   package Nested with Always_Terminates is
      procedure Nested_Proc;
   end Nested;

end Functions;
