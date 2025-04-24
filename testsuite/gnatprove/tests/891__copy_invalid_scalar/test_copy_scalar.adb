procedure Test_Copy_Scalar with Spark_Mode is

   procedure Test_Assign with Global => null is
      X : Positive with Size => 64, Potentially_Invalid, Import;
      Y : Positive with Size => 32, Potentially_Invalid;
   begin
      Y := X; --  @VALIDITY_CHECK:FAIL
      pragma Assert (X'Valid = Y'Valid);
   end Test_Assign;

   procedure Test_Decl with Global => null is
      X : Positive with Size => 64, Potentially_Invalid, Import;
      Y : Positive := X with Size => 32, Potentially_Invalid; --  @VALIDITY_CHECK:FAIL
   begin
      pragma Assert (X'Valid = Y'Valid);
   end Test_Decl;

begin
   null;
end;
