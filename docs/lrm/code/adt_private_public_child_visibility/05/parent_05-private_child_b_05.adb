package body Parent_05.Private_Child_B_05
is
   function H (X : Integer) return Integer is
      Result : Integer;
   begin
      if X <= 10 then
         Result := 10;
      else
         Result := Parent_05.F (X);  -- Illegal in SPARK 2005
      end if;
      return Result;
   end H;
end Parent_05.Private_Child_B_05;
