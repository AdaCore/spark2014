pragma Extensions_Allowed (All_Extensions);

function Test9 return Integer is
begin
   return X : Integer := 0 do
      null;
      return;
   finally
      X := 1;
      begin
         X := 2;
      finally
         X := 3;
      end;
   end return;
end;
