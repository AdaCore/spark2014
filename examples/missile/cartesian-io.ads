-- I/O for cartesian package
-- Not SPARK
-- $Log: cartesian-io.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.1  2003/08/10 20:15:26  adi
-- Initial revision
--
--
with Cartesian;
package Cartesian.IO is

   procedure Get_Position(P : out Position);
   procedure Get_Velocity(V : out Velocity);
   procedure Get_Accel(A : out Accel);

end Cartesian.IO;

