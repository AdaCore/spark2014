pragma SPARK_Mode (On);
package body Parent_14.Public_Child_A_14
is
   function G (X : Integer) return Integer is
      Result : Integer;
   begin
      if X <= 0 then
         Result := 0;
      else
         Result := Parent_14.F (X);  -- OK
      end if;
      return Result;
   end G;
end Parent_14.Public_Child_A_14;
