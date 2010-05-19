-- Check cartesian data
-- $Log: cartesian-check.adb,v $
-- Revision 1.3  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/10 22:01:08  adi
-- Initial revision
--
--
with Test.Checking;
with Measuretypes.Checks;
package body Cartesian.Check is
   procedure Position
     (S        : in String;
      Expected : in Cartesian.Position;
      Actual   : in Cartesian.Position;
      Margin   : in Measuretypes.Meter)
   is begin
      Measuretypes.Checks.Meter_M
	(S        => S & " x",
	 Expected => Expected.X,
	 Actual   => Actual.X,
	 Margin   => Margin);
      Measuretypes.Checks.Meter_M
	(S        => S & " y",
	 Expected => Expected.y,
	 Actual   => Actual.y,
	 Margin   => Margin);
      Measuretypes.Checks.Meter_M
	(S        => S & " z",
	 Expected => Expected.z,
	 Actual   => Actual.z,
	 Margin   => Margin);
   end Position;

   procedure Velocity
     (S        : in String;
      Expected : in Cartesian.Velocity;
      Actual   : in Cartesian.velocity;
      Margin   : in Measuretypes.Meter_Per_Sec)
   is begin
      Measuretypes.Checks.Meter_Per_Sec_M
	(S        => S & " vx",
	 Expected => Expected.vX,
	 Actual   => Actual.vX,
	 Margin   => Margin);
      Measuretypes.Checks.Meter_Per_Sec_M
	(S        => S & " vy",
	 Expected => Expected.vy,
	 Actual   => Actual.vy,
	 Margin   => Margin);
      Measuretypes.Checks.Meter_Per_Sec_M
	(S        => S & " vz",
	 Expected => Expected.vz,
	 Actual   => Actual.vz,
	 Margin   => Margin);
   end Velocity;

   procedure Accel
     (S        : in String;
      Expected : in Cartesian.Accel;
      Actual   : in Cartesian.Accel;
      Margin   : in Measuretypes.Cm_Per_Sec_2)
   is begin
      Measuretypes.Checks.Cm_Per_Sec_2_M
	(S        => S & " ax",
	 Expected => Expected.aX,
	 Actual   => Actual.aX,
	 Margin   => Margin);
      Measuretypes.Checks.Cm_Per_Sec_2_M
	(S        => S & " ay",
	 Expected => Expected.ay,
	 Actual   => Actual.ay,
	 Margin   => Margin);
      Measuretypes.Checks.Cm_Per_Sec_2_M
	(S        => S & " az",
	 Expected => Expected.az,
	 Actual   => Actual.az,
	 Margin   => Margin);
   end Accel;

end Cartesian.Check;
