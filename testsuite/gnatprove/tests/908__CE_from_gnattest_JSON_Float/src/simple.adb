package body Simple
with SPARK_Mode
is

   function Div_Float (N : Float) return Float is
   begin
      return 1.0 / (N - 3.1415);
   end Div_Float;

end Simple;
