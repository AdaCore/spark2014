procedure Main
is
   function Return_5 return Natural
   is
   begin
      return 5;
   end Return_5;

   Temp : Natural := 0;
begin
   for I in 1 .. Return_5 loop
      Temp := Temp + I;
   end loop;
end main;
