procedure Loop_Param (Z : Integer) is
begin
   for J in Integer range 1 .. Z loop
      declare
         K : Integer with Address => J'Address, Import;
      begin
         K := 0;
      end;
   end loop;
end Loop_Param;
