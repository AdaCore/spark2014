pragma SPARK_Mode (On);
package body Parent_14.Private_Child_B_14
is
   function H (X : Integer) return Integer is
      Result : Integer;
   begin
      if X <= 10 then
         Result := 10;
      else
         Result := Parent_14.F (X);  -- Legal in SPARK 2014
      end if;
      return Result;
   end H;
end Parent_14.Private_Child_B_14;
