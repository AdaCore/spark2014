package body Interval
  with SPARK_Mode => On
is

   function Make(Low, High : Float) return Interval is
   begin
      if Low <= High then
         return (Low, High);
      else
         return (High, Low);
      end if;
   end Make;

end Interval;
