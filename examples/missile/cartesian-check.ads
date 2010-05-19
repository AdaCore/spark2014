-- Check cartesian data
-- $Log: cartesian-check.ads,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/10 20:51:07  adi
-- Initial revision
--
--
with Cartesian,Measuretypes;
--# inherit Cartesian,Measuretypes;
package Cartesian.Check is
   procedure Position
     (S        : in String;
      Expected : in Cartesian.Position;
      Actual   : in Cartesian.Position;
      Margin   : in Measuretypes.Meter);

   procedure Velocity
     (S        : in String;
      Expected : in Cartesian.Velocity;
      Actual   : in Cartesian.Velocity;
      Margin   : in Measuretypes.Meter_Per_Sec);

   procedure Accel
     (S        : in String;
      Expected : in Cartesian.Accel;
      Actual   : in Cartesian.Accel;
      Margin   : in Measuretypes.Cm_Per_Sec_2);
end Cartesian.Check;
