procedure Main is
   type T is mod 15;
   X : T := 10;

   procedure Test (Y : out Natural) with Pre => True is
      Hi : T;
   begin
      Y := 0;
      Hi := X;
      for J in 0 .. Hi loop -- Hi is >= 0, so loop will execute at least once
         Y := Y + 1;
      end loop;
   end;
   Y : Natural;
begin
   Test (Y);
end;
