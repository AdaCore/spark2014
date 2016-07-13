pragma SPARK_Mode;
With Ada.Unchecked_Conversion;

procedure Typconv (X : Integer; Y : out Short_Integer) is
   function Conv is new Ada.Unchecked_Conversion (Integer, Short_Integer);
begin
   Y := Conv (X);
end Typconv;
