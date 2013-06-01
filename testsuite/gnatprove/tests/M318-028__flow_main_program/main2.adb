with Some_Package;

function Main2 return Natural
   with Global => (Some_Package.X, Some_Package.State)
is
   Temp : Natural := 0;
begin
   for I in 1 .. Some_Package.X loop
      Temp := Temp + I;
   end loop;
   return Temp;
end Main2;
