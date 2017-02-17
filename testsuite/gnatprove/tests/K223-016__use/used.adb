package body Used is
   function Absolu (x : Integer) return Integer is
      Res : Integer;
   begin
      if x < 0 then
         Res := -x;
      else
         Res := x;
      end if;
      return Res;
   end Absolu;
end Used;
