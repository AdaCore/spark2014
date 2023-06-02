procedure Reclaim_Call_3 is
   type T is access Integer;
   X : T := new Integer'(123);
   procedure Panic
     with Global => null,
          Exceptional_Cases => (Program_Error    => True,
                                Constraint_Error => True),
          Always_Terminates => True,
          Import;
begin
   begin
      declare
         Y : access Integer := X;
      begin
         if Y.all mod 2 = 0 then
            Y.all := 456;
            Panic;  --  Y should be reclaimed on the path to exception handler
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
