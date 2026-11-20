package body Flow_Op
  with SPARK_Mode
is

   ---------
   -- "&" --
   ---------

   function "&" (Left, Right : Integer) return Integer is
   begin
      if Left = 0 then
         Stop;
      end if;
      return Right;
   end;

   ---------
   -- "&" --
   ---------

   function "&" (Left, Right : Boolean) return Boolean is
   begin
      if Left then
         Stop;
      end if;
      return Right;
   end;

end;
