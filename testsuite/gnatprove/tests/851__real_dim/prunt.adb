package body Prunt with
  SPARK_Mode => On
is

   function Crackle_At_Time (T1 : Time; T : Time) return Crackle is
   begin
      if T < T1 then
         return 0.0 * mm / s**5;
      elsif T < 2.0 * s then
         return 0.0 * mm / s**5;
      elsif T < 3.0 * T1 then
         return 0.0 * mm / s**5;
      else
         return 0.0 * mm / s**5;
      end if;
   end Crackle_At_Time;

end Prunt;
