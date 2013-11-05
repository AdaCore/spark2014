package body Parent_05.Public_Child_A_05
is
   function G (X : Integer) return Integer is
      Result : Integer;
   begin
      if X <= 0 then
         Result := 0;
      else
         Result := Parent_05.F (X);  -- OK
      end if;
      return Result;
   end G;
end Parent_05.Public_Child_A_05;
