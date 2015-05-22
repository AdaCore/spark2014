package body P is

  procedure Never_Return
    with No_Return,
         Pre => True
  is
  begin
     loop
        null;
     end loop;
  end Never_Return;

  procedure OK is
  begin
     Never_Return;
  end OK;

  procedure OK_2 is
  begin
     pragma Assert (Dummy in Integer);
     Never_Return;
  end OK_2;

end P;
