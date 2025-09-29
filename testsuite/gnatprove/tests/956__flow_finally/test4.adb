pragma Extensions_Allowed (All_Extensions);

procedure Test4 (C : Boolean; Y : out Boolean) is
begin
   if C then
      Y := False;  --  unused assignment
   else
      return;
   end if;
finally
   Y := True;
end;
