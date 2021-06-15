procedure Main_Elsif (A : Boolean; Y : out Integer) is
   X : Integer;
begin
   if A then
      Y := 0;
   elsif X = 0 then
      Y := X;
   else
      Y := 2;
   end if;
end Main_Elsif;
