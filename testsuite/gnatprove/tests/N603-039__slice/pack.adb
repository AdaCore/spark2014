package body Pack is

   Glob   : String := "qwertyuiopasdfghjklzxcvbnm";

   procedure A2 is
      My_S2 : String (1 .. 4) := Glob (1 .. 4); -- @INDEX_CHECK:FAIL
   begin
      null;
   end A2;

end Pack;
