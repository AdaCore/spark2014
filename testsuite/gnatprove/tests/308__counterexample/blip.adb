package body blip is


function Square (X : in Integer) return Integer
  with SPARK_Mode
is
begin
   return X * X;
   end Square;

end blip;
