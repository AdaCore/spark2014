with Const; use Const;

procedure Client (B1, B2 : Boolean) is
begin
   if B1 then
      pragma Assert (C.D = 10_000);  --  @ASSERT:FAIL
   elsif B2 then
      pragma Assert (Get = 10_000);  --  @ASSERT:FAIL
   else
      pragma Assert (Get2 = 10_000);  --  @ASSERT:PASS
   end if;
end Client;
