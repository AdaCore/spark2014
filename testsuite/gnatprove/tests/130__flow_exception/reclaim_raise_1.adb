procedure Reclaim_Raise_1 is
   type T is access Integer;
   X : T := new Integer'(123);
begin
   declare
      Y : access Integer := X;
   begin
      Y.all := 456;
      raise Program_Error;  --  Y should NOT be reclamed on the path to handler
   exception
      when Program_Error =>
         Y.all := 654;
   end;
   X.all := 789;
end;
