with Data;

procedure Validate with
  Post => Data.Sensor_Valid = Data.Sensor'Valid
is
begin
   Data.Sensor_Valid := Data.Sensor'Valid;
end Validate;
