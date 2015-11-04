function Concat_String (S : String) return String
  with SPARK_Mode
is
   S1 : String := S & ";";
   S2 : String := "value is " & Integer'Image(32);
begin
   return S1 & S2;
end Concat_String;
