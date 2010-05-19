-- Checking for measuretypes
--
-- $Log: measuretypes-checks.ads,v $
-- Revision 1.4  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
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
-- Revision 1.4  2003/08/27 20:51:37  adi
-- Added Kelvin
--
-- Revision 1.3  2003/08/25 20:04:06  adi
-- Added bit4 array and slice checks
--
-- Revision 1.2  2003/08/25 13:55:29  adi
-- Corrected namings
--
-- Revision 1.1  2003/08/25 13:49:47  adi
-- Initial revision
--
--
with MeasureTypes;
--# inherit measuretypes, test;
package Measuretypes.checks is
   procedure Bit4_Slice(S : in String;
                        Expected, Actual : in Measuretypes.Bit4_Slice);
   --# global in out test.state;
   --# derives test.state from *, S, Expected,actual;

   procedure Bit4_Array(S : in String;
                        Expected, Actual : in Measuretypes.Bit4_Array);
   --# global in out test.state;
   --# derives test.state from *, S, Expected,actual;


   procedure Kelvin(S : in String;
                    Expected,
                      Actual : in MeasureTypes.Kelvin);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Meter(S : in String;
                    Expected,
                      Actual : in MeasureTypes.Meter);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;
   
   procedure Meter_M
     (S : in String;
      Expected,
      Actual : in MeasureTypes.Meter;
      Margin : in Measuretypes.Meter);
   --# global in out Test.State;
   --# derives
   --#  Test.State from *, S, Expected, Actual, Margin;

   procedure Newton(S : in String;
                    Expected,
                    Actual : in MeasureTypes.Newton;
                   Margin : in MeasureTypes.Newton);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual, Margin;

   procedure Kilo(S : in String;
                  Expected,
                    Actual : in MeasureTypes.kilo);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Meter_2(S : in String;
                  Expected,
                    Actual : in MeasureTypes.Meter_2);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Meter_Per_sec(S : in String;
                    Expected,
                      Actual : in MeasureTypes.Meter_Per_Sec);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;
   
   procedure Meter_Per_Sec_M
     (S : in String;
      Expected,
      Actual : in MeasureTypes.Meter_Per_Sec;
      Margin : in Measuretypes.Meter_Per_Sec);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual, Margin;

   procedure Gram_Per_sec(S : in String;
                    Expected,
                      Actual : in MeasureTypes.gram_Per_Sec);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Meter_Per_Sec_2(S : in String;
                    Expected,
                      Actual : in MeasureTypes.Meter_Per_Sec_2);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Cm_Per_Sec_2
     (S : in String;
      Expected,
      Actual : in MeasureTypes.cm_Per_Sec_2);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;
   
   procedure Cm_Per_Sec_2_M
     (S : in String;
      Expected,
      Actual : in MeasureTypes.cm_Per_Sec_2;
      Margin : in Measuretypes.Cm_Per_Sec_2);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual, Margin;

   procedure Millirad_Per_Sec(
      S : in String;
      Expected, Actual : in Measuretypes.Millirad_Per_Sec);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   -- Angle checks can be done involving degrees (user expected)
   --  and/or millirads (internal form)
   procedure Angle_Degrees
     (S : in String;
      Expected : in Measuretypes.Angle_Degrees;
      Actual   : in Measuretypes.Angle_Degrees);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Angle_Degrees_Millirads
     (S : in String;
      Expected : in Measuretypes.Angle_Degrees;
      Actual   : in Measuretypes.Millirad);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

   procedure Angle_Millirad
     (S : in String;
      Expected : in Measuretypes.Millirad;
      Actual   : in Measuretypes.Millirad);
   --# global in out Test.State;
   --# derives Test.State from *, S, Expected, Actual;

end Measuretypes.checks;
