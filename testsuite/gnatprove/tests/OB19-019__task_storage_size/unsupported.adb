procedure p is
   type R is array (Natural) of Character;
   type P is access all R;
   for P'Storage_Size use 0;
   --  Above access type intended only for interfacing purposes

   y : P;

begin
   null;
end;
