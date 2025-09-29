pragma Extensions_Allowed (All_Extensions);

procedure Test6 (C : Boolean; Y : out Boolean) is
begin
   if C then
      begin
         if C then
            return;
         end if;
      finally
         Y := False;  --  unused assignment
      end;
   else
      return;
   end if;
finally
   Y := True;
end;
