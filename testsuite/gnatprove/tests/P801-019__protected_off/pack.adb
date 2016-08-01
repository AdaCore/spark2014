package body Pack is

   protected body Prot is
      procedure P is
      begin
         B := not B;
         X := X + 1;
      end P;

      entry E
      with SPARK_Mode => Off
      when B is
      begin
         P;
         X := X + 1;
      end E;
   end Prot;

end Pack;
