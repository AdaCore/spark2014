package body P with SPARK_Mode is

   function Copy (X : T) return T is
   begin
      if X = null then
         return null;
      else
         return new Integer'(X.all);
      end if;
   end Copy;

end P;
