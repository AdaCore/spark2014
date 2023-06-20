procedure Reclaim_Raise_3 is
   type T is access Integer;
   X : T := new Integer'(123);
begin
   begin
      declare
         Y : access Integer := X;
      begin
         if Y.all mod 2 = 0 then
            Y.all := 456;
            raise Program_Error;
         elsif Y.all mod 2 = 1 then
            Y.all := 456;
            raise Constraint_Error;
         else
            Y.all := 789;
         end if;
      exception
         when Constraint_Error =>
            Y.all := 456;
      end;
   exception
      when Program_Error =>
         pragma Assert (X.all in 456 | 789);
   end;
end;
