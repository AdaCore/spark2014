pragma Extensions_Allowed (All_Extensions);

procedure Test_Bad_No_Raise with SPARK_Mode is
   procedure P_1 with
     No_Raise,
     Exceptional_Cases => (Constraint_Error => True);
   procedure P_1 is
   begin
      raise Constraint_Error;
   end P_1;
   procedure P_2 with
     No_Raise,
     Exit_Cases => (True => Exception_Raised);
   procedure P_2 is
   begin
      raise Constraint_Error;
   end P_2;
   procedure P_3 with
     No_Raise,
     Exit_Cases => (True => (Exception_Raised => Constraint_Error));
   procedure P_3 is
   begin
      raise Constraint_Error;
   end P_3;
begin
   null;
end;
