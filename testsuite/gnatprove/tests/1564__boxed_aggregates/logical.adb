procedure Logical (Value : Integer; Result : out Integer) with
  SPARK_Mode, Pre => Value = 0
is
   type I is new Integer with Relaxed_Initialization;
   type A is array (1 .. 2) of I;
   function F return A is ((others => <>));
   X : A := F;
begin
   Result := Value;
   pragma Assert (Result = 1); -- @ASSERT:FAIL
end Logical;
