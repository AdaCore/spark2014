with Q;

procedure P.Priv_Proc is
begin
   loop
      P.X := not P.X;
   end loop;
end;
