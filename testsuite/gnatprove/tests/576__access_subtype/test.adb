procedure Test with SPARK_Mode is
   package P_Access is
      type T is private;
   private
      type T is access STRING with Type_Invariant => True;
      Z : T(1..5) := new STRING'("CCCCC");
   end P_Access;
begin
   null;
end Test;
