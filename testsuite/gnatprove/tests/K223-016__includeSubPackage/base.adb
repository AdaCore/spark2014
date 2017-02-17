with Base.Annex;

package body Base is pragma SPARK_Mode (On);
   function Double (x : Integer) return Integer is
   begin
      return Annex.Mul (2, x);
   end Double;
end Base;
