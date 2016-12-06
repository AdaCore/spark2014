procedure Exprfun
  with SPARK_Mode
is
   type T1 is null record;
   T1_Var : T1;
   function Prim_Func return T1 is (T1_Var);

   X : T1;
begin
   X := Prim_Func;
   pragma Assert (False);
end Exprfun;
