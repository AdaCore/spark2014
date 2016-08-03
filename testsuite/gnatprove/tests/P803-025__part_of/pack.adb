package body Pack is

   protected body Prot is
      procedure P is
      begin
         B := not B;
         Pack.X := 1;
      end P;
   end Prot;

end Pack;
