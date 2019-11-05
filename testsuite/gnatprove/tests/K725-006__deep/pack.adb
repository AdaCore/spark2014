procedure Pack
  with Global => null
is
   generic
      type T1 is (<>);
   package Genpack is
      package Apack with Initializes => (Ary, Bpack.Bry) is
         type    T is array (Integer range <>) of Boolean;
         Ary   : T(1..4) := (True,False,True,False);

         package Bpack with Initializes => Bry is
            type    Q is array (Integer range <>) of Boolean;
            Bry   : Q(1..4) := (True,False,True,False);
         end Bpack;
      end Apack;
   end Genpack;

   package Mypack is new Genpack (T1 => Integer);

begin
   if Mypack.Apack."/="(Mypack.Apack.Ary,(True, False, True, False)) then
      null;
   end if;

   if Mypack.Apack.Bpack."/="(Mypack.Apack.Bpack.Bry,(True, False, True, False))
     then
      null;
   end if;
end Pack;
