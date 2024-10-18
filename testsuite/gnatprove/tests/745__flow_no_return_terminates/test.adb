procedure Test with SPARK_Mode is
   procedure Raise_CE with
     Exceptional_Cases => (Constraint_Error => True),
     No_Return;

   procedure Raise_CE is
   begin
      raise Constraint_Error;
   end Raise_CE;

   procedure P with
     Always_Terminates,
     Exceptional_Cases => (Constraint_Error => True),
     No_Return;

   procedure P is
   begin
      Raise_CE;
   end P;
begin
   null;
end Test;
