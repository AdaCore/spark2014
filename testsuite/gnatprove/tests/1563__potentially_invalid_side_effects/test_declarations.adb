pragma Extensions_Allowed (On);

procedure Test_Declarations with SPARK_Mode is
   type R is record
      F : Positive;
   end record;

   function Read return R with
     Import, Side_Effects, Always_Terminates, Global => null,
     Potentially_Invalid => Read'Result;

   procedure Check_Result with Global => null is
   begin
      X : constant R := Read; --  @VALIDITY_CHECK:FAIL
      pragma Assert (X.F > 0);
   end Check_Result;

   procedure Propagate_Result with Global => null is
   begin
      X : constant R := Read with Potentially_Invalid;
      pragma Assert (X'Valid_Scalars); --  @ASSERT:FAIL
   end Propagate_Result;

   function Extended_Return return R with
     Side_Effects, Global => null;

   function Extended_Return return R is
   begin
      return X : R := Read do --  @VALIDITY_CHECK:FAIL
         null;
      end return;
   end Extended_Return;
begin
   null;
end Test_Declarations;
