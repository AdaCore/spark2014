package body Over is

   function F (X, Y : T) return T is
      Res : T;
   begin
      if 100 - X < Y then
         Res := (X + Y) - 100;
      else
         Res := X + Y;
      end if;
      return Res;
   end;

end Over;
