with P;
with P.C2;

procedure Main (Dummy : Float) is
   package IP is new P;
   package I2 is new IP.C2;
begin
   null;
end;
