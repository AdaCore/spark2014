-- Checking for measuretypes
--
-- $Log: measuretypes-checks.adb,v $
-- Revision 1.5  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.4  2004/12/17 17:51:22  adi
-- Fixed compass angle conversions and checks so that compass.in passes
--
-- Revision 1.3  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.2  2004/12/12 16:08:14  adi
-- Moved most type checking functions from test.Checking to Measuretypes.Checks as they should be
-- Added clarifications to compass.in as partial explanation of why errors appearing
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/08/27 20:51:28  adi
-- Added Kelvin
--
-- Revision 1.2  2003/08/25 20:03:56  adi
-- Added bit4 array and slice tests
--
-- Revision 1.1  2003/08/25 13:55:32  adi
-- Initial revision
--
--
-- This is not SPARK, just Ada
with Test;
with Measuretypes.Angle_Ops;
package body Measuretypes.checks is
   procedure Bit4_Slice(S : in String;
                        Expected, Actual : in Measuretypes.Bit4_Slice)
   is begin
      Test.Align(S);
      if Expected(0) = Actual(0) and
        Expected(1) = Actual(1) and
        Expected(2) = Actual(2) and
        Expected(3) = Actual(3) then
         Test.Pass(" ");
      else
         Test.Fail("A=[" &
                   Boolean'Image(Actual(0)) &
                   "," &
                   Boolean'Image(Actual(1)) &
                   "," &
                   Boolean'Image(Actual(2)) &
                   "," &
                   Boolean'Image(Actual(3)) &
                   "]");
      end if;
   end Bit4_Slice;

   procedure Bit4_Array(S : in String;
                        Expected, Actual : in Measuretypes.Bit4_Array)
   is begin
      Bit4_Slice(S & " (0) ",
                 Expected(0),
                 Actual(0));
      Bit4_Slice(S & " (1) ",
                 Expected(1),
                 Actual(1));
      Bit4_Slice(S & " (2) ",
                 Expected(2),
                 Actual(2));
      Bit4_Slice(S & " (3) ",
                 Expected(3),
                 Actual(3));
   end Bit4_array;

   procedure Kelvin(S : in String;
                   Expected,
                     Actual : in MeasureTypes.kelvin)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Kelvin'Image(Expected) &
                     "K, A=" & MeasureTypes.kelvin'Image(Actual) &
                  "K");
      end if;
   end Kelvin;

   procedure Meter
     (S : in String;
      Expected,
      Actual : in MeasureTypes.Meter)
   is begin
      Meter_M(S        => S, 
	      Expected => Expected,
	      Actual   => Actual,
	      Margin   => 0);
   end Meter;
   
   procedure Meter_M
     (S : in String;
      Expected,
      Actual : in MeasureTypes.Meter;
      Margin : in Measuretypes.Meter)
   is begin      
      Test.Align(S);
      if (Expected >= Actual and then Actual+Margin >= Expected) or
	(Actual > Expected and then Expected+Margin >= Actual) then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Meter'Image(Expected) &
                     "m, A=" & MeasureTypes.Meter'Image(Actual) &
                     "m");
      end if;
   end Meter_M;

   procedure Newton(S : in String;
                    Expected,
                    Actual : in MeasureTypes.Newton;
                    Margin : in MeasureTypes.Newton)
   is begin
      Test.Align(S);
      if (Expected >= Actual and then
            Actual + Margin >= Expected) or
        (Actual > Expected and then
           Expected + Margin >= Actual) then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Newton'Image(Expected) &
                     "N, A=" & MeasureTypes.newton'Image(Actual) &
                     "N");
      end if;
   end Newton;

   procedure Kilo(S : in String;
                  Expected,
                    Actual : in MeasureTypes.kilo)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Kilo'Image(Expected) &
                     "Kg, A=" & MeasureTypes.kilo'Image(Actual) &
                  "Kg");
      end if;
   end Kilo;

   procedure Meter_2(S : in String;
                  Expected,
                    Actual : in MeasureTypes.Meter_2)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Meter_2'Image(Expected) &
                     "m^2, A=" & MeasureTypes.Meter_2'Image(Actual) &
                     "m^2");
      end if;
   end Meter_2;

   procedure Meter_Per_Sec
     (S : in String;
      Expected,
      Actual : in MeasureTypes.Meter_Per_Sec)
   is begin
      Meter_Per_Sec_M
	(S => S, 
	 Expected => Expected,
	 Actual   => Actual,
	 Margin   => 0);
   end Meter_Per_Sec;
   
   procedure Meter_Per_Sec_M
     (S : in String;
      Expected,
      Actual : in MeasureTypes.Meter_Per_Sec;
      Margin : in Measuretypes.Meter_Per_Sec)
   is begin
     Test.Align(S);
     if (Expected >= Actual and then Actual+Margin >= Expected) or
        (Actual > Expected and then Expected+Margin >= Actual) then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Meter_Per_Sec'Image(Expected) &
                     "m/s, A=" & Measuretypes.Meter_Per_Sec'Image(Actual) &
                  "m/s");
      end if;
   end Meter_Per_Sec_M;

   procedure Gram_Per_sec(S : in String;
                       Expected,
                         Actual : in MeasureTypes.gram_Per_Sec)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Gram_Per_Sec'Image(Expected) &
                     "g/s, A=" & Measuretypes.gram_Per_Sec'Image(Actual) &
                  "g/s");
      end if;
   end Gram_Per_sec;

   procedure Meter_Per_Sec_2(S : in String;
                    Expected,
                      Actual : in MeasureTypes.Meter_Per_Sec_2)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Meter_Per_Sec_2'Image(Expected) &
                     "m/s^2, A=" & Measuretypes.Meter_Per_Sec_2'Image(Actual) &
                     "m/s^2");
      end if;
   end Meter_Per_Sec_2;

   procedure Cm_Per_Sec_2
     (S : in String;
      Expected,
      Actual : in MeasureTypes.cm_Per_Sec_2)
   is begin
      Cm_Per_Sec_2_M
	(S => S,
	 Expected => Expected,
	 Actual   => Actual,
	 Margin   => 0);
   end Cm_Per_Sec_2;
   
   procedure Cm_Per_Sec_2_M
     (S : in String;
      Expected,
      Actual : in MeasureTypes.cm_Per_Sec_2;
      Margin : in Measuretypes.Cm_Per_Sec_2)
   is begin
      Test.Align(S);
      if (Expected >= Actual and then Actual+Margin >= Expected) or
	 (Actual > Expected and then Expected+Margin >= Actual) then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Cm_Per_Sec_2'Image(Expected) &
                     "cm/s^2, A=" & Measuretypes.cm_Per_Sec_2'Image(Actual) &
                  "cm/s^2");
      end if;
   end Cm_Per_Sec_2_M;

   procedure Millirad_Per_Sec(S : in String;
                    Expected,
                      Actual : in MeasureTypes.Millirad_Per_Sec)
   is begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" & Measuretypes.Millirad_Per_Sec'Image(Expected) &
                     "mR/s, A=" & Measuretypes.Millirad_Per_Sec'Image(Actual) &
                  "mR/s");
      end if;
   end Millirad_Per_Sec;

   -- Compare angles in degrees
   procedure Angle_Degrees
     (S        : in String;
      Expected : in Measuretypes.Angle_Degrees;
      Actual   : in Measuretypes.Angle_Degrees)
   is
   begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      elsif (Actual > Expected and then (Actual-Expected = 1)) or
        (Expected > Actual and then (Expected-Actual = 1)) then
         Test.Pass(" (within rounding)");
      else
         Test.Fail("E=" &
                     Measuretypes.Angle_Degrees'Image(Expected) &
                     "deg , A=" &
                     Measuretypes.Angle_Degrees'Image(Actual) &
                     "deg");
      end if;
   end Angle_Degrees;

   -- Compare angles in Degrees *and* Millirads
   procedure Angle_Degrees_Millirads
     (S        : in String;
      Expected : in Measuretypes.Angle_Degrees;
      Actual   : in Measuretypes.Millirad)
   is
      Actual_Deg : Measuretypes.Angle_Degrees;
   begin
      Test.Align(S);
      Actual_Deg := Measuretypes.Angle_Ops.Round_Degree(Actual);
      if Expected = Actual_Deg then
         Test.Pass(" ");
      elsif (Actual_Deg > Expected and then (Actual_Deg - Expected = 1)) or
        (Expected > Actual_Deg and then (Expected - Actual_Deg = 1)) then
         Test.Pass(" (withing rounding) ");
      else
         Test.Fail("E=" &
                     Measuretypes.Angle_Degrees'Image(Expected) &
                     "mR , A=" &
                     Measuretypes.Angle_Degrees'Image(Actual_Deg) &
                     "mR");
      end if;
   end Angle_Degrees_Millirads;

   -- Compare angles in Millirads
   procedure Angle_Millirad
     (S        : in String;
      Expected : in Measuretypes.Millirad;
      Actual   : in Measuretypes.Millirad)
   is
   begin
      Test.Align(S);
      if Expected = Actual then
         Test.Pass(" ");
      else
         Test.Fail("E=" &
                     Measuretypes.Millirad'Image(Expected) &
                     "mR , A=" &
                     Measuretypes.Millirad'Image(Actual) &
                     "mR");
      end if;
   end Angle_Millirad;

end Measuretypes.checks;
