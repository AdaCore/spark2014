procedure P is
  L : constant Natural := 21;

  generic
     LP : in Natural;
  procedure Q;

  procedure Q is
  begin
     null;
  end Q;

  procedure QI is new Q (LP => L) ;

begin
   null;

end P;
