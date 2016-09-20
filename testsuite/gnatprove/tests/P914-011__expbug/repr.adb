package body Repr is

   Limit : constant LONG_FLOAT := 10.0;
   Buf     : array (0 .. 3) of Float;

function F return Integer with Pre => True;

function F return Integer is
begin
   return 2;
end F;

procedure Check is

begin
      if ((LONG_FLOAT(Buf(F))**2)) < Limit then
         null;
      else
         null;
      end if;

end Check;

   procedure P is null;

end Repr;
