procedure Base is
   pragma SPARK_Mode(On);
   X : Integer := 0;

   function P (X : Integer) return Integer is (X + 1);
begin
   X := P (X);
end Base;
