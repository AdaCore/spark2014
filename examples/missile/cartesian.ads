-- Cartesian types and operations
--
-- $Log: cartesian.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.2  2003/08/10 18:07:46  adi
-- Added constants
--
-- Revision 1.1  2003/08/10 17:13:09  adi
-- Initial revision
--
--
with Measuretypes;
--# inherit measuretypes;
package Cartesian
is

   type Position is record
      X, Y, Z : Measuretypes.Meter;
   end record;

   type Velocity is record
      Vx, Vy, Vz : Measuretypes.Meter_Per_Sec;
   end record;

   type Accel is record
      Ax, Ay, Az : Measuretypes.Cm_Per_Sec_2;
   end record;

   Zero_Position : constant Position :=
     Position'(X => 0, Y => 0, Z => 0);

   Zero_velocity: constant velocity :=
     Velocity'(vX => 0, vY => 0, vZ => 0);

   Zero_accel : constant accel :=
     accel'(aX => 0, aY => 0, aZ => 0);

end Cartesian;

