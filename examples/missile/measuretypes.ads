-- Types for measuring physical phenomena
--
-- $Log: measuretypes.ads,v $
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
-- Revision 1.17  2003/08/26 18:26:06  adi
-- Added Kelvin
--
-- Revision 1.16  2003/08/25 13:25:27  adi
-- Added bit grids and slices
--
-- Revision 1.15  2003/08/22 18:20:25  adi
-- Added 40 and 45 millirad constants
--
-- Revision 1.14  2003/08/18 18:19:23  adi
-- Added 10,20,30 millirad angles
--
-- Revision 1.13  2003/08/12 18:29:56  adi
-- Added gram_per_sec
--
-- Revision 1.12  2003/08/11 18:28:14  adi
-- Added area
--
-- Revision 1.11  2003/08/08 19:15:11  adi
-- Split off operations to Angle_Ops
--
-- Revision 1.10  2003/08/06 21:00:42  adi
-- Added meter_per_sec_2
--
-- Revision 1.9  2003/08/04 20:35:20  adi
-- Added degree_to_millirad
--
-- Revision 1.8  2003/08/03 19:05:46  adi
-- Added Millirad_to_word
--
-- Revision 1.7  2003/08/03 18:55:24  adi
-- Added Int_To_Millirads
--
-- Revision 1.6  2003/08/02 19:42:27  adi
-- Added round_Degree
--
-- Revision 1.5  2003/08/02 19:31:30  adi
-- Added Angle type
--
-- Revision 1.4  2003/08/02 19:13:37  adi
-- Added ability to translate a word to an angle
--
-- Revision 1.3  2003/08/02 18:05:02  adi
-- Added Millirad type and operations
--
-- Revision 1.2  2003/02/09 20:54:41  adi
-- Added non-neg subtypes
--
-- Revision 1.1  2003/02/09 20:09:00  adi
-- Initial revision
--
--
with Systemtypes;
--# inherit Systemtypes;
package MeasureTypes is

   -- Distance
   type Meter is range -200_000 .. 200_000;
   --# assert Meter'base is long_integer;
   subtype Pos_Meter is Meter range 0..Meter'Last;
   -- Position
   type Location is record
      X : Meter;
      Y : Meter;
      Z : Meter;
   end record;

   -- Area
   type Meter_2 is range 0..1000;
   --# assert Meter_2'base is integer;

   -- Velocity (scalar)
   type Meter_Per_Sec is range -5000 .. 5000;
   --# assert meter_per_sec'base is integer;
   subtype Pos_Meter_Per_Sec is Meter_Per_Sec range 0..Meter_Per_Sec'Last;
   -- Velocity (vector)
   type Velocity is record
      DX : Meter_Per_Sec;
      DY : Meter_Per_Sec;
      DZ : Meter_Per_Sec;
   end record;

   -- Acceleration (scalar)
   type Meter_Per_Sec_2 is range -200 .. 200;
   --# assert meter_per_sec_2'base is integer;
   type Cm_Per_Sec_2 is range -30_000 .. 30_000;
   --# assert cm_per_sec_2'base is integer;

   -- Mass
   type Kilo is range 0..20_000;
   --# assert kilo'base is integer;

   -- Mass rate
   type Gram_Per_Sec is range 0..30_000;
   --# assert gram_per_sec'base is integer;

   -- Temperature
   type Kelvin is range 0..6_000;
   --# assert kelvin'base is integer;

   -- Force
   type Newton is range -1_000_000 .. 1_000_000;
   --# assert newton'base is long_integer;

   -- Bit grids
   type Bit_Range is range 0..255;
   subtype bit4_Range is Bit_Range range 0..3;
   subtype Bit8_Range is Bit_Range range 0..7;
   subtype Bit16_Range is Bit_Range range 0..15;

   type Bit4_Slice  is array(bit4_Range) of Boolean;
   type Bit8_Slice  is array(bit8_Range) of Boolean;
   type Bit16_Slice is array(bit16_Range) of Boolean;

   type Bit4_Array is array(Bit4_range) of Bit4_Slice;
   type Bit8_Array is array(Bit8_range) of Bit8_Slice;
   type Bit16_Array is array(Bit16_range) of Bit16_Slice;


   -- Public angle for text entry purposes
   type Angle_Degrees is range 0..359;

   -- Angle: (-pi,+pi] radians
   -- Private type to prevent dumb handling
   type Millirad is private;
   Angle_Zero, Angle_Right, Angle_Left,
     Angle_Half, Angle_Minushalf : constant Millirad;
   Ten_Millirads    : constant Millirad;
   Twenty_Millirads : constant Millirad;
   Thirty_Millirads : constant Millirad;
   Forty_Millirads : constant Millirad;
   Fortyfive_Millirads : constant Millirad;
   Hundred_Millirads : constant Millirad;

   -- Rate of change of angle: from -2 to 2 rads/sec
   type Millirad_per_sec is range -2_000 .. 2000;
   Angle_Rate_Zero : constant Millirad_per_sec := 0;
   
private
   -- Private millirad type

   type Millirad is range -7000 .. 7000;
   --# assert Millirad'base is Integer;

   Angle_Zero : constant Millirad := 0;
   Angle_Left : constant Millirad := -1571;
   Angle_Right : constant Millirad := 1572;
   Angle_Half : constant Millirad := 3142;
   Angle_Full : constant Millirad := 6283;
   Angle_Minushalf : constant Millirad := -3142;

   Ten_Millirads    : constant Millirad := 10;
   Twenty_Millirads : constant Millirad := 20;
   Thirty_Millirads : constant Millirad := 30;
   Forty_Millirads : constant Millirad  := 40;
   Fortyfive_Millirads : constant Millirad := 45;
   Hundred_Millirads : constant Millirad := 100;

   subtype Canon_Millirad is Millirad range (Angle_Minushalf+1) .. Angle_half;
   subtype Pos_milliRad is Millirad range 0 .. Angle_half;

end MeasureTypes;

