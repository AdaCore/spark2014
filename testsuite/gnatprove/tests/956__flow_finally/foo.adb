pragma Extensions_Allowed (All_Extensions);

function Foo return Integer is
begin
   return X : Integer do
      X := 0;
   finally
      X := 1;
      begin
         X := 2;
      finally
         X := 3;
      end;
   end return;
end;
