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

   function Select_Bullet2 return Bullet'Class is
      E : Gun_Bullet'Class := Gun_Bullet'(others => <>);
   begin
      pragma Assert (Hit (E) in 0 .. 10);
      return E;
   end Select_Bullet2;

end Weapon_Class;
