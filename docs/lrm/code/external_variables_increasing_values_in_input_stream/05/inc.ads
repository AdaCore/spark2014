 package Inc
--# own in Sensor : Integer;
is
   procedure Increases (Result : out Boolean;
                        Valid  : out Boolean);
   --# global in Sensor;
   --# post Valid -> (Result <-> Sensor'Tail (Sensor~) > Sensor~);

end Inc;
