package body Base.Annex is pragma SPARK_Mode (On);
   function Mul (x : Integer; y : Integer) return Integer is
   begin
      return x * y;
   end Mul;
end Base.Annex;
