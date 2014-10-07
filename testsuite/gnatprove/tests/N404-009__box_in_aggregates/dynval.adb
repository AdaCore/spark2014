procedure Dynval (L, U : Integer) with
  SPARK_Mode
is
   subtype T is Integer range L .. U;
   type A is array (T) of T with Default_Component_Value => 5;  --  @RANGE_CHECK:FAIL
   X : A;
begin
   X := A'(others => <>);
end Dynval;
