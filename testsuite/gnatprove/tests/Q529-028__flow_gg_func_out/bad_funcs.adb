package body Bad_Funcs with SPARK_Mode => Off is
   function Bad return Boolean is
   begin
      if G < Integer'Last then
         G := G + 1;
         return True;
      end if;
      return False;
   end Bad;
end Bad_Funcs;
