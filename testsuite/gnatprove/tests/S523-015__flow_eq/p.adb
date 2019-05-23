package body P is

   V : Boolean := True;

   function "=" (X, Y : T) return Boolean is
   begin
      if V then
         return True;
      else
         return False;
      end if;
   end "=";
end P;
