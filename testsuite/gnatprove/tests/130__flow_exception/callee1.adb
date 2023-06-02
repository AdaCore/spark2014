procedure Callee1
  with Global => null
is
   type By_Copy is new Integer;

   type By_Reference is limited record
      C : Integer;
   end record;

   type By_Unspecified is record
      C : Integer;
   end record;

   procedure Test
     (By_C : out By_Copy;
      By_R : out By_Reference;
      By_U : out By_Unspecified)
   with
     Exceptional_Cases => (Program_Error => True)
   is
   begin
      raise Program_Error;
   end Test;

   C : By_Copy;
   R : By_Reference;
   U : By_Unspecified;

begin
   Test (C, R, U);
exception
   when Program_Error =>
      null;
end;
