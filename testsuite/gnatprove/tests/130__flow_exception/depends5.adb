procedure Depends5
  with Global => null
is
   type By_Unspecified is record
      C : Integer;
   end record;

   procedure Test (X : Integer; Y : out By_Unspecified)
     with Exceptional_Cases => (Program_Error => True),
          Depends => (Y => X)
   is
   begin
      if X > 0 then
         Y.C := X;
      else
         raise Program_Error;
      end if;
   end Test;

   Z : By_Unspecified := (C => 456);
begin
   Test (123, Z);
exception
   when Program_Error =>
      pragma Assert (Z.C = 456);  --  @INITIALIZED:CHECK
end;
