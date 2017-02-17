package body Over is

   function F (X, Y : T) return T is
      Res : T;
   begin
      if X > 50 and then Y > 50 then
         Res := (X + Y) - 100;
      else
         Res := X;
      end if;
      return Res;
   end;

end Over;
