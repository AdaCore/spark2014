procedure Multi_Induction (X1, X2 : out Integer; Y : in Integer) is
begin
   X1 := 0;
   X2 := 0;
   while X1 < Y loop
      X1 := X1 + 2;
      X2 := X2 + 6;
   end loop;
end Multi_Induction;
