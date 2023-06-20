procedure Reclaim_Raise_2 is
   type T is access Integer;
   X : T := new Integer'(123);
begin
   begin
      declare
         Y : access Integer := X;
      begin
         if Y.all mod 2 = 0 then
            Y.all := 456;
            raise Program_Error;  --  Y should be reclaimed on the path to handler
         else
            Y.all := 789;
         end if;
      end;
   exception
      when Program_Error =>
         pragma Assert (X.all in 456 | 789);
   end;
end;
