with Density_Altitude.Temperature_Unit,
     Density_Altitude.Pressure_Unit,
     Density_Altitude.Humidity_Unit;
package body Density_Altitude
   with SPARK_Mode    => On,
        Refined_State => (Density_State => (Temperature_Unit.Temp_State,
                                            Pressure_Unit.Press_State,
                                            Humidity_Unit.Humid_State)) is
   procedure Read (Value : out Feet)
      with Refined_Global  => (Input  => (Temperature_Unit.Temp_State,
                                          Pressure_Unit.Press_State,
                                          Humidity_Unit.Humid_State)),
           Refined_Depends => (Value  => (Temperature_Unit.Temp_State,
                                          Pressure_Unit.Press_State,
                                          Humidity_Unit.Humid_State)),
           SPARK_Mode => Off  --  use conversion from fixed to float
   is
      Temperature : Temperature_Unit.Degrees;
      Pressure    : Pressure_Unit.PSI;
      Humidity    : Humidity_Unit.Percent;
   begin
      Temperature_Unit.Read (Temperature);
      Pressure_Unit.Read (Pressure);
      Humidity_Unit.Read (Humidity);
      Value := Feet (Float (Temperature) +  -- A stub for the real
                     Float (Pressure) +     -- equation that calculates
                     Float (Humidity));     -- density altitude
   end Read;

end Density_Altitude;
