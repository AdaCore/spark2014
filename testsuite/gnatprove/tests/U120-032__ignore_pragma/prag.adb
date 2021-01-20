pragma Ignore_Pragma (Assert);
procedure Prag (X : in out Integer) is
begin
   pragma Assert (X = 42);
end Prag;
