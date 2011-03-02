package body Used is
   function Absolu (x : Integer) return Integer is
   begin
      if x < 0 then
         return -x;
      end if;
      return x;
   end Absolu;
end Used;
