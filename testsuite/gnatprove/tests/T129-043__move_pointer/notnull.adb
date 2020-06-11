pragma SPARK_Mode;
procedure Notnull is
   type T is access Integer;
   X, Y : T;
begin
   X := new Integer'(0);
   for I in 1 .. 10 loop
      Y := X;
   end loop;
end Notnull;
