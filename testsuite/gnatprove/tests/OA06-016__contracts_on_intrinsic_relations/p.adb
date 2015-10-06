package body P
  with SPARK_Mode => On
is

   procedure Proc1 (X : Time_Span) is
   begin
      if X > 0 then
         null;
      else
         --  this branch is unreachable
         raise Constraint_Error;
      end if;
   end;

   procedure Proc2 (X : Time_Span) is
   begin
      if abs (X) >= 0 then
         null;
      else
         --  this branch is unreachable
         raise Constraint_Error;
      end if;
   end;

end;
