-- Implementation of Airspeed LRU logging
--
-- $Log: airspeed-log.adb,v $
-- Revision 1.1  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
--
with Bit_Machine;
package body Airspeed.Log
is
   Unit_Name : constant String := "Airspeed";

   Unit_Header : constant String :=
        "Speed(m/s) Acceleration(cm/s^2) ";

   function Header return Logging_Cfg.Log_String
   is
   begin
      return Logging_Cfg.Log_String_Ops.To_Bounded_String
	(Unit_Name & ": " & Unit_Header);
   end Header;

   procedure Data(Ans : out Logging_Cfg.Log_String)
   is
      Speed_Now : Airspeed.Meter_Per_Sec;
      Accel_Now : Airspeed.Cm_Per_Sec_2;
      --Bit_Status : BIT_Machine.Machine;
   begin
      Airspeed.Read_Airspeed(Speed_Now);
      Accel_Now := Airspeed.Read_Accel;
      --BIT_Status := Airspeed.Read_BIT_Status;
      Ans := Logging_Cfg.Log_String_Ops.To_Bounded_String
	(Unit_Name & ": "
	   & Airspeed.Meter_Per_Sec'Image(Speed_Now) & " "
	   & Airspeed.Cm_Per_Sec_2'Image(Accel_Now) & " "
	);
      --& Bit_Machine.Machine'Image(BIT_Status) & " ";
   end Data;

end Airspeed.Log;
