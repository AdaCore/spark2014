procedure Test_String with SPARK_Mode is
   Str : String := "0";
begin
   pragma Assert (Integer'Value (Str) = 0);
   --  Unprovable do to imprecise handling of 'Value
end Test_String;
