procedure Test_Force_Analysis_Inline with SPARK_Mode, Program_Exit => True is

   --  Check that the detection of potential abnormal termination works even
   --  with inlining.

   procedure I is
   begin
      raise Program_Error; -- @RAISE:FAIL
   end I;

   function F (B : Boolean) return Boolean is
   begin
      if B then
         I;
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

   procedure I2 is
   begin
      Do_Raise; -- @RAISE:FAIL
   end I2;

   function F2 (B : Boolean) return Boolean is
   begin
      if B then
         I2;
      end if;
      return True;
   end F2;

   procedure Do_Exit with
     Program_Exit => True,
     Always_Terminates,
     No_Return,
     Global => null,
     Import;

   procedure I3 is
   begin
      Do_Exit; -- @UNEXPECTED_PROGRAM_EXIT:FAIL
   end I3;

   function F3 (B : Boolean) return Boolean is
   begin
      if B then
         I3;
      end if;
      return True;
   end F3;

   procedure Does_Not_Terminate (B : Boolean) with
     Always_Terminates => B,
     No_Return,
     Global => null,
     Import;

   procedure I4 is
   begin
      Does_Not_Terminate (False); -- @TERMINATION:FAIL
   end I4;

   function F4 (B : Boolean) return Boolean is
   begin
      if B then
         I4;
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
