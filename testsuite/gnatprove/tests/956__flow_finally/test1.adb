pragma Extensions_Allowed (All_Extensions);

procedure Test1 is
begin
   begin
      null;
   finally
      declare
         procedure Test       --  Check that flow scope is created for Test
           with Pre => True
         is
         begin
            null;
         end;
      begin
         Test;
      end;
   end;
end;
