pragma SPARK_Mode(On);
package body Tank1
with
  Refined_State => (Tank_State => The_Tank)
is
   -- Cylinder Tank
   type Tank_Type is
      record
         Crossection_Area : Float;
         Height           : Float;
         Max_Volume       : Float;
         Cur_Volume       : Float;
         H_Sensor_Loc     : Float;
         L_Sensor_Loc     : Float;
      end record
        with Predicate => (Cur_Volume <= Max_Volume);

   -- This is the hidden data structure for package
   The_Tank : Tank_Type;

   function Valid_Sensors return boolean
   is
      (if The_Tank.H_Sensor_Loc <= The_Tank.Cur_Volume then
          The_Tank.L_Sensor_Loc <= The_Tank.Cur_Volume);

   function Valid_Tank return Boolean
   is
      (The_Tank.Crossection_Area > 0.0 and then
       The_Tank.Height > 0.0 and then
       The_Tank.Cur_Volume >= 0.0 and then
       The_Tank.Cur_Volume <= The_Tank.Height and then
       The_Tank.H_Sensor_Loc > The_Tank.L_Sensor_Loc and then
       The_Tank.L_Sensor_Loc >= 0.0 and then
       The_Tank.H_Sensor_Loc <= The_Tank.Height and then
       Valid_Sensors);

end;
