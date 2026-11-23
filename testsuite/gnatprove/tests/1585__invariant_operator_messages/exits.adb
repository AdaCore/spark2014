package body Exits with SPARK_Mode is

   ---------
   -- "&" --
   ---------

   function "&" (Left, Right : Integer) return Integer is
   begin
      if Left < 0 then
         raise E;
      elsif Left = 0 then
         Stop;
      else
         return Right;
      end if;
   end "&";
end Exits;
