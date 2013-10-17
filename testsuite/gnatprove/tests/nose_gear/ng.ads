with Interfaces; use Interfaces;

package NG is

   subtype Mod_Time is Unsigned_16;
   subtype Mod_Distance is Unsigned_16;
   subtype Mod_Count is Unsigned_16;
   subtype Time is Natural;
   subtype Distance is Natural;
   subtype Count is Natural;
   subtype Velocity is Natural;

   EstimatedGroundVelocityIsAvailable : Boolean := False;
   EstimatedGroundVelocity : Velocity;

   --  Global constants

   WHEEL_DIAMETER : constant := 26;
   WHCF : constant := (((WHEEL_DIAMETER * 254) / 7) * 22) / 100;

   --  Global data saved between invocations

   PrevTime  : Mod_Time := 0;
   PrevCount : Mod_Count := 0;

   procedure UpdateNGVelocity;
end NG;
