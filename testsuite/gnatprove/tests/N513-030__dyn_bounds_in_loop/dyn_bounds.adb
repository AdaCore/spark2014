procedure Dyn_Bounds (C : Natural) with SPARK_Mode is
begin
   for I in 1 .. C loop
      declare
         subtype Simple is Natural range 0 .. I;
         subtype With_Expr is Integer range -I .. I;

         function F_Simple_1 (C : Natural) return Boolean is
           (C in Simple'Range);

         function F_Simple_2 (C : Simple) return Simple with
           Pre  => C < Simple'Last,
           Post => F_Simple_2'Result > Simple'First;

         function F_Simple_2 (C : Simple) return Simple is
           (C + 1);

         function F_With_Expr_1 (C : Integer) return Boolean is
           (C in With_Expr'Range);

         function F_With_Expr_2 (C : With_Expr) return With_Expr with
           Pre  => C < With_Expr'Last,
           Post => F_With_Expr_2'Result > With_Expr'First;

         function F_With_Expr_2 (C : With_Expr) return With_Expr is
           (C + 1);
      begin
         null;
      end;
   end loop;
end;
