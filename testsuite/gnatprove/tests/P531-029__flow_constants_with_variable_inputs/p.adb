package body P
with SPARK_Mode => On is

   procedure any (a : in integer; b : out integer) is

      x : constant integer := a;

      function reference_param_via_constant return Integer is
         (x);
   begin
      b := reference_param_via_constant;
   end;

end P;
