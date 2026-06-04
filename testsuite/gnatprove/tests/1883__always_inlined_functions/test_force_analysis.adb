procedure Test_Force_Analysis with SPARK_Mode, Program_Exit => True is

   --  Functions should not have side-effects. They should not cause the
   --  subprogram to fail to return normally even if the calling context allows
   --  it.

   function F (B : Boolean) return Boolean is
   begin
      if B then
         raise Program_Error; -- @RAISE:FAIL
      end if;
      return True;
   end F;

   procedure Do_Raise with
     Exceptional_Cases =>
       (Constraint_Error => True),
     Always_Terminates,
     No_Return,
     Global => null,
     Import;

   function F2 (B : Boolean) return Boolean is
   begin
      if B then
         Do_Raise; -- @RAISE:FAIL
      end if;
      return True;
   end F2;

   procedure Do_Exit with
     Program_Exit => True,
     Always_Terminates,
     No_Return,
     Global => null,
     Import;

   function F3 (B : Boolean) return Boolean is
   begin
      if B then
         Do_Exit; -- @UNEXPECTED_PROGRAM_EXIT:FAIL
      end if;
      return True;
   end F3;

   procedure Does_Not_Terminate (B : Boolean) with
     Always_Terminates => B,
     No_Return,
     Global => null,
     Import;

   function F4 (B : Boolean) return Boolean is
   begin
      if B then
         Does_Not_Terminate (False); -- @TERMINATION:FAIL
      end if;
      return True;
   end F4;

   function G (X, Y, Z, U : Boolean) return Boolean is (X or Y or Z or U);

begin
   if G (F (True), F2 (True), F3 (True), F4 (True)) then
      null;
   end if;
exception
   when Program_Error =>
      null;
   when Constraint_Error =>
      null;
end;
