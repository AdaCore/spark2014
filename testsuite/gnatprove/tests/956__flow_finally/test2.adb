pragma Extensions_Allowed (All_Extensions);

procedure Test2 is
   X : Integer;
begin
   begin
      null;
   finally
      declare
         subtype S is Integer range 1 .. X;  --  Check that sanity tests apply
      begin
         null;
      end;
   end;
end;
