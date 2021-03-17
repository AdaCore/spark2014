package body Eval is
   procedure Extract (A : My_Array; J : Integer; V : out Value) is
   begin
      if J in A'Range then
         V := A(J);
      else
         V := 0;
      end if;
   end Extract;
end Eval;
