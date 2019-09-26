procedure Noret (X : in Integer; Y : out Integer)
  with SPARK_Mode, Global => null
is
   procedure Error with No_Return, Global => null is
   begin
      raise Program_Error;
   end Error;

begin
   if X > 0 then
      Error;
   end if;
   Y := 0;
end Noret;
