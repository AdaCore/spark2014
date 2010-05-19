-- I/O for measuretypes
--
-- $Log: measuretypes-io.ads,v $
-- Revision 1.3  2004/12/17 17:51:22  adi
-- Fixed compass angle conversions and checks so that compass.in passes
--
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/27 20:49:34  adi
-- Added Kelvin
--
-- Revision 1.1  2003/08/18 18:16:31  adi
-- Initial revision
--
with Ada.Text_Io, MeasureTypes, Systemtypes;
package Measuretypes.io is
   -- Measure units data
   package Kelvin_Io is
      new Ada.Text_Io.Integer_Io(Measuretypes.Kelvin);
   package Meter_Io is
      new Ada.Text_Io.Integer_Io(MeasureTypes.Meter);
   package Speed_Io is
      new Ada.Text_Io.Integer_Io(Measuretypes.Meter_Per_Sec);
   package Accel_Io is
      new Ada.Text_Io.Integer_Io(Measuretypes.Meter_Per_Sec_2);
   package Accel_Cm_Io is
      new Ada.Text_Io.Integer_Io(Measuretypes.Cm_Per_Sec_2);
   package Mass_Io is
      new Ada.Text_Io.Integer_Io(Measuretypes.Kilo);
   package Gram_Rate_Io is
      new Ada.Text_Io.Integer_Io(Measuretypes.Gram_Per_Sec);
   package Force_Io is
      new Ada.Text_Io.Integer_Io(Measuretypes.Newton);
   package Angle_Rate_Io is 
      new Ada.Text_IO.Integer_IO(Measuretypes.Millirad_Per_sec);

   -- Angle resolution is in single degrees
   package Angle_Io is new Ada.Text_IO.Integer_Io(Measuretypes.Angle_Degrees);

   -- Display Millirad as string
   function Millirad(r : in millirad) return String;

end Measuretypes.io;
