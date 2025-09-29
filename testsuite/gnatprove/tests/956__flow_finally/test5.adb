pragma Extensions_Allowed (All_Extensions);

procedure Test5 (C : Boolean; Y : out Boolean) is
begin
   if C then
      begin
         return;
      finally
         Y := False;  --  unused assignment
      end;
   else
      return;
   end if;
finally
   Y := True;
end;
