package Exprfun is

   A : Boolean;
   B : Boolean;

   function Valid return Boolean is (A and then B);

   procedure P with Post => Valid;
end Exprfun;
