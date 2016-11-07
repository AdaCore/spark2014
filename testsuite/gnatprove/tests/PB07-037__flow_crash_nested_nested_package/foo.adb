procedure Foo
is
begin
   declare
      package A is
         package B is
            N : Integer := 666;
         end B;
      end A;

      package body A is
         package body B is
         end B;
      end A;

   begin
      if A.B.N = 42 then
         null;
      end if;
   end;
end Foo;
