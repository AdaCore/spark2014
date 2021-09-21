package body P with SPARK_Mode => Off is
   function F return Boolean is
   begin
      return X = null;
   end;
end;
