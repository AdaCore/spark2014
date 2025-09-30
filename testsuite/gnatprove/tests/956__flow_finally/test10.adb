pragma Extensions_Allowed (All_Extensions);

procedure Test10 (Y : out Boolean) is
begin
   return;
finally
   goto L;
   Y := False;
   <<L>>
   Y := True;
end;
