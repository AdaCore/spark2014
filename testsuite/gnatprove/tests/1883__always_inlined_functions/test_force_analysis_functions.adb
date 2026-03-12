procedure Test_Force_Analysis_Functions with SPARK_Mode, Program_Exit => True is

   --  Test with function calls with side effects

   function Do_Raise return Boolean with
     Side_Effects,
     Exceptional_Cases =>
       (Constraint_Error => True),
     Always_Terminates,
     Global => null,
     Import;

   function F2 (B : Boolean) return Boolean is
      C : Boolean;
   begin
      if B then
         C := Do_Raise; -- @RAISE:FAIL
      end if;
      return True;
   end F2;

   function Do_Exit return Boolean with
     Side_Effects,
     Program_Exit => True,
     Always_Terminates,
     Global => null,
     Import;

   function F3 (B : Boolean) return Boolean is
      C : Boolean;
   begin
      if B then
         C := Do_Exit; -- @UNEXPECTED_PROGRAM_EXIT:FAIL
      end if;
      return True;
   end F3;

   function Does_Not_Terminate (B : Boolean) return Boolean with
     Side_Effects,
     Always_Terminates => B,
     Global => null,
     Import;

   function F4 (B : Boolean) return Boolean is
      C : Boolean;
   begin
      if B then
         C := Does_Not_Terminate (False); -- @TERMINATION:FAIL
      end if;
      return True;
   end F4;

   function G (Y, Z, U : Boolean) return Boolean is (Y or Z or U);

begin
   if G (F2 (True), F3 (True), F4 (True)) then
      null;
   end if;
exception
   when Program_Error =>
      null;
   when Constraint_Error =>
      null;
end;
