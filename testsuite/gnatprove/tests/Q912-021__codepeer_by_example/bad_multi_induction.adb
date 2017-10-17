procedure Bad_Multi_Induction (X1, X2 : out Integer; Y : in Positive) is
begin
   X1 := 0;
   X2 := 0;
   while X1 < Y loop
      X2 := X2 + 6;
   end loop;
end Bad_Multi_Induction;
