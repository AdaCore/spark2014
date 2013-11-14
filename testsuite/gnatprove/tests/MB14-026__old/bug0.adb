package body Bug0 is
   pragma Spark_Mode;

   procedure Bug (S : in out String) is
      Old :  String := S;
   begin
      pragma Assert (Old = S);
   end;

end Bug0;
