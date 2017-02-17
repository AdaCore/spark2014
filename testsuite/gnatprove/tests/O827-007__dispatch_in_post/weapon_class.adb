package body Weapon_Class
with SPARK_Mode
is

   function Hit (Self : Gun_Bullet) return Integer is
   begin
      return 2;
   end Hit;


   function Select_Bullet return Bullet'Class is
   begin
      return Gun_Bullet'(others => <>);
   end Select_Bullet;

end Weapon_Class;
