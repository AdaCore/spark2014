with Const; use Const;

procedure Client (B1, B2 : Boolean) is 
begin
   if B1 then
      pragma Assert (C = 10_000);  --  should be unprovable
   elsif B2 then
      pragma Assert (Get = 10_000);  --  should be unprovable
   else
      pragma Assert (Get2 = 10_000);
   end if;
end Client;
