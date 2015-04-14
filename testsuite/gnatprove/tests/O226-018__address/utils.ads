with Interfaces; use Interfaces;

package Utils is
   --  Types
   subtype Allowed_Floats is Float range -100_000.0 .. 100_000.0;

   --  Constants
   PORT_MAX_DELAY  : constant Unsigned_32     := 16#ffffffff#;
   IMU_UPDATE_FREQ : constant Allowed_Floats := 500.0;
   IMU_UPDATE_DT   : constant Allowed_Floats := 1.0 / IMU_UPDATE_FREQ;


end Utils;
