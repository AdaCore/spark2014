package body P with SPARK_Mode => Off is

   function "=" (X, Y : T) return Boolean is
   begin
      return Ctx and then X.C = Y.C;
   end "=";

end P;
