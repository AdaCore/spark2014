-- Trig for angles
--
-- $Log: measuretypes-angle_ops-trig.ads,v $
-- Revision 1.2  2004/12/17 16:08:53  adi
-- Fixing errors in compass; renamed Angle to Angle_Degrees for clarity
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/09/07 19:29:31  adi
-- Initial revision
--
--

with Measuretypes.Angle_ops;
--# inherit Measuretypes,measuretypes.angle_ops;
package Measuretypes.Angle_Ops.trig is

   function Arctan2(X, Y : Measuretypes.Meter)
     return Measuretypes.Angle_Degrees;

end Measuretypes.Angle_Ops.trig;

