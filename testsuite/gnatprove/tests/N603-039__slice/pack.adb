package body Pack is

   Glob   : String := "qwertyuiopasdfghjklzxcvbnm";

   procedure A2 is
      My_S2 : String (1 .. 35) := Glob (1 .. 35);
   begin
      null;
   end A2;

end Pack;
