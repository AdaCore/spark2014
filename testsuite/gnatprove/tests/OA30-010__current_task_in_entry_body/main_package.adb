package body Main_Package is

   protected body PT is
      entry E when Flag is
      begin
         P.S1;
      end E;
   end PT;

begin
   null;
end Main_Package;
