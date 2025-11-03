procedure Test with SPARK_Mode is

   procedure Test1 is
      pragma Assertion_Policy (Ghost => Ignore);
      procedure Raise_PE (B : Boolean) with Ghost is
      begin
         if B then
            raise Program_Error; --  @RAISE:FAIL

         end if;
      end Raise_PE;
   begin
      Raise_PE (True);
      raise Constraint_Error;
   exception
      when Program_Error =>
         null;
   end Test1;

   procedure Test2 is
      pragma Assertion_Policy (Ghost => Ignore);
      procedure Raise_PE (B : Boolean) with Ghost is
      begin
         if B then
            raise Program_Error; --  @RAISE:FAIL

         end if;
      end Raise_PE;

      procedure Call_Raise_PE (B : Boolean) with Ghost is
      begin
         Raise_PE (B);
      end Call_Raise_PE;

   begin
      Call_Raise_PE (True);
      raise Constraint_Error;
   exception
      when Program_Error =>
         null;
   end Test2;

   procedure Test3 is
      pragma Assertion_Policy (Ghost => Ignore);
      procedure Raise_PE (B : Boolean) with Ghost is
      begin
         if B then
            raise Program_Error; --  Ok, it is caught before going to non-ghost code
         end if;
      end Raise_PE;

      procedure Call_Raise_PE  with Ghost is
      begin
         begin
            Raise_PE (True);
            raise Constraint_Error;
         exception
            when Program_Error =>
               null;
         end;
      end Call_Raise_PE;

   begin
      Call_Raise_PE;
   end Test3;
begin
   Test1;
end;
