with Interfaces.C.Extensions; use Interfaces.C.Extensions;

package Stabilizer_Pack
with SPARK_Mode,
  Abstract_State => (Asl_Parameters,
                     Asl_Variables),
  Initializes => (Asl_Parameters,
                  Asl_Variables)

is
private

   --  Global variables and constants

   --  Altitude variables
   Temperature  : Float := 0.0
     with Part_Of => Asl_Variables; --  Temperature from barometer
   Pressure     : Float := 1000.0
     with Part_Of => Asl_Variables; --  Pressure from barometer
   Asl          : Float := 0.0
     with Part_Of => Asl_Variables; --  Smoothed asl
   Asl_Raw      : Float := 0.0
     with Part_Of => Asl_Variables; --  Raw asl
   Asl_Long     : Float := 0.0
     with Part_Of => Asl_Variables; --  Long term asl

   --  Altitude parameters
   Asl_Err_Deadband : Float := 0.00
     with Part_Of => Asl_Parameters; --  error (target - altitude) deadband
   Asl_Alpha        : Float := 0.92
     with Part_Of => Asl_Parameters; --  Short term smoothing
   Asl_Alpha_Long   : Float := 0.93
     with Part_Of => Asl_Parameters; --  Long term smoothing

   --  Function called when Alt_Hold mode is activated. Holds the drone
   --  at a target altitude.
   procedure Stabilizer_Alt_Hold_Update
     with
       Global => (Input => (Asl_Parameters,
                            Asl_Variables));

end Stabilizer_Pack;
