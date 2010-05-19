-- Cartesian IO implementation
-- $Log: cartesian-io.adb,v $
-- Revision 1.2  2005/01/24 19:19:05  adi
-- Hacked to implement logging
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/10 20:15:42  adi
-- Initial revision
--
--
with Measuretypes.Io;
package body Cartesian.Io is

   procedure Get_Position(P : out Position)
   is begin
      Measuretypes.Io.Meter_Io.Get(P.x);
      Measuretypes.Io.Meter_Io.Get(P.Y);
      Measuretypes.Io.Meter_Io.Get(P.Z);
   end Get_Position;

   procedure Get_velocity(V : out velocity)
   is   begin
      Measuretypes.Io.Speed_Io.Get(V.vx);
      Measuretypes.Io.Speed_Io.Get(V.vY);
      Measuretypes.Io.Speed_Io.Get(V.vZ);
   end Get_velocity;

   procedure Get_Accel(A : out Accel)
   is begin
      Measuretypes.Io.Accel_cm_Io.Get(A.Ax);
      Measuretypes.Io.Accel_Cm_Io.Get(A.Ay);
      Measuretypes.Io.Accel_Cm_Io.Get(A.Az);
   end Get_Accel;

end Cartesian.Io;
