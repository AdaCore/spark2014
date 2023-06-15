procedure Test with SPARK_Mode is
   procedure A with Import, Global => null, Always_Terminates;
   procedure B with Import, Global => null, Always_Terminates;

   procedure C with Import, Global => null, Always_Terminates;
   package D with Always_Terminates is
   end D;
   procedure E with Import, Global => null;
begin
   null;
end Test;
