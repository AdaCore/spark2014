pragma SPARK_Mode;

procedure Bad is
   procedure P (X : String) with Pre => True is
      Lo : Positive := X'First;  --  @RANGE_CHECK:FAIL
   begin
      null;
   end P;

   Bad_Lo : String (-1 .. -2) := (others => ' ');
begin
   P (Bad_Lo);
end Bad;
