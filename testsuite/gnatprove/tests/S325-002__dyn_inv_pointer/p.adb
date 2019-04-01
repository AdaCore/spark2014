procedure P with SPARK_Mode is
begin
   for I in 1 .. 10 loop
      declare
         type List_D;

         type List_Acc is access List_D;

         type List_D (D : Boolean) is record
            Val  : Integer;
            Next : List_Acc;
         end record
           with Predicate => (if D then Val > I);

         function F (X : List_Acc) return Integer is
           (X.Next.Next.Val)
           with Pre => X /= null and then X.Next /= null and then X.Next.Next /= null,
           Post => (if X.Next.Next.D then F'Result > I);

         function H (X : List_Acc) return Integer is
           (X.Next.Val)
           with Pre => X /= null and then X.Next /= null,
           Post => H'Result > I; --@POSTCONDITION:FAIL
      begin
         null;
      end;
   end loop;
end P;
