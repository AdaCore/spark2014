pragma Extensions_Allowed (All_Extensions);

procedure Test7 (Y : out Boolean) is
begin
   begin
      goto L;
   finally
      Y := False;  --  unused assignment
   end;
   <<L>>
finally
   Y := True;
end;
