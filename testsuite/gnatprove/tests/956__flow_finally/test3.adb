pragma Extensions_Allowed (All_Extensions);

procedure Test3 is
begin
   begin
      null;
   finally
      declare
         A : Boolean;

         procedure Flip
           with Pre => True, Global => null --  Check that GG picks Flip
         is
         begin
            A := not A;
         end;
      begin
         Flip;
      end;
   end;
end;
