procedure Reclaim_Call_1 is
   type T is access Integer;
   X : T := new Integer'(123);
   procedure Panic
     with Global => null,
          Exceptional_Cases => (Program_Error => True),
          Always_Terminates => True,
          Import;
begin
   declare
      Y : access Integer := X;
   begin
      Y.all := 456;
      Panic;   --  Y should NOT be reclaimed on the path to exception handler
   exception
      when Program_Error =>
         Y.all := 654;
   end;
   X.all := 789;
end;
