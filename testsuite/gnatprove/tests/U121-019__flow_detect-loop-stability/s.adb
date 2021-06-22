procedure S is
   X, Y : Boolean := True;
begin
   while X loop
      while Y loop
         X := not X;
      end loop;
   end loop;
end S;
