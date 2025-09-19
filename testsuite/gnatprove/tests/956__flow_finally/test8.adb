pragma Extensions_Allowed (All_Extensions);

procedure Test8 is
   X : Boolean := True;
begin
   for J in 1 .. 3 loop
      begin
         goto L;
      finally
         null; --pragma Assert (X = X'Loop_Entry);
      end;
      <<L>>
      null;
   end loop;
end;
