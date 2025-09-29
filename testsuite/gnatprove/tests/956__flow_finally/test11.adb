pragma Extensions_Allowed (All_Extensions);

procedure Test11 (Y : out Boolean) is
begin
   return;
finally
   for J in 1 .. 100 loop
      exit;
      Y := False;
   end loop;
   Y := True;
end;
