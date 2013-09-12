procedure P is 

     generic
          type priv is private;
     package gen_p is
        T : Integer;
     end gen_p;

     package P is new gen_p(Integer);

  begin
   null;

  end P;
