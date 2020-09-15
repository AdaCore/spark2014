package body P is
   procedure A (Cond : Boolean) is
   begin
      if Cond then A (not Cond); end if;
   end;
end;
