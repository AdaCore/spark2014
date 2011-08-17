procedure Pack is
   generic
      type T1 is (<>);
   package Genpack is
      package Apack is
         type    T is array (Integer range <>) of Boolean;
         Ary   : T(1..4) := (True,False,True,False);
      end Apack;
   end Genpack;

   package Mypack is new Genpack (T1 => Integer);

begin
   if Mypack.Apack."/="(Mypack.Apack.Ary,(True, False, True, False)) then
      null;
   end if;

end Pack;
