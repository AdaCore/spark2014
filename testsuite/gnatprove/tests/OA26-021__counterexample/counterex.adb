procedure Counterex (R : out Integer) with
  SPARK_Mode
is
   Result : Integer;
begin
   Result := 42;
   pragma Assert (Result < 42);
   R := Result;
end Counterex;
