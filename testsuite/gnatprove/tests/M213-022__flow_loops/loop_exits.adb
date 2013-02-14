procedure Loop_Exits (X : in out Integer;
                      Y : in Integer)
is
begin

   My_Loop : loop
      X := 0;
      for I in Integer range 0 .. 10 loop
         X := I;
         exit My_Loop when X > Y;
      end loop;
      X := X;
   end loop My_Loop;
   X := 5;

end Loop_Exits;
