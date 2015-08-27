package Weapon_Class
with SPARK_Mode
is

   subtype Cycle_Time is Integer range 0 .. 30;

   ------------------
   -- Bullet class --
   ------------------

   type Bullet is abstract tagged record
      null;
   end record;

   function Hit (Self : Bullet) return Integer is abstract
   with Post'Class => Hit'Result < 12;

   type Gun_Bullet is new Bullet with record
      null;
   end record;

   function Hit (Self : Gun_Bullet) return Integer
     with Post'Class => Hit'Result in 0 .. 10;

   ------------------
   -- Ennemy class --
   ------------------

   function Select_Bullet return Bullet'Class with
     Post => Hit (Select_Bullet'Result) in 0 .. 10;
end Weapon_Class;
