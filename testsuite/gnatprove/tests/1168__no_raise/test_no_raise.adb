pragma Extensions_Allowed (All_Extensions);

procedure Test_No_Raise with SPARK_Mode is
   procedure P1 with
     No_Raise;
   procedure P1 is
   begin
      raise Constraint_Error; -- @RAISE:FAIL
   end P1;

   procedure P2 with
     No_Raise;
   procedure P2 is
   begin
      raise Constraint_Error; -- @RAISE:NONE
   exception
      when Constraint_Error => null;
   end P2;
begin
   null;
end;
