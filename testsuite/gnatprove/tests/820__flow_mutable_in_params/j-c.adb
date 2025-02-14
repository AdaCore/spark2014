package body J.C with SPARK_Mode => Off is

   procedure P (X : T) is
   begin
      if G /= null and X /= null then
         X.all := G.all;
         G := null;
      end if;
   end P;

end J.C;
