with Exc;
with Gen_Exc;

procedure Client (X : Integer) is
   package G1 is new Gen_Exc (1);
   package G2 is new Gen_Exc (2);
begin
   if X = 0 then
      raise Exc.Bad;
   elsif X = 1 then
      raise G1.Too_Bad;
   else
      raise G2.Bad;
   end if;
end Client;
