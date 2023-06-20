procedure Callee2
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
      By_C2:     By_Copy;
      By_R : out By_Reference;
      By_U : out By_Unspecified)
   with
     Exceptional_Cases => (Program_Error => True)
   is
   begin
      By_U.C := Integer (By_C2);
      raise Program_Error;
   end Test;

   C : By_Copy;
   C2: By_Copy := 123;
   R : By_Reference;
   U : By_Unspecified;

begin
   Test (C, C2, R, U);
exception
   when Program_Error =>
      null;
end;
