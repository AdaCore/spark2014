-- Flying_object
-- Provide a private type describing an object
--  and tracking its motion
-- $Log: flying_object.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/08/11 19:24:39  adi
-- Time-extrapolate position and velocity on read
--
-- Revision 1.2  2003/08/11 18:39:06  adi
-- Added  null_entity
--
-- Revision 1.1  2003/08/11 18:02:06  adi
-- Initial revision
--
--
with Measuretypes,Cartesian,clock;
use type Measuretypes.Meter,
  Measuretypes.Meter_Per_sec;
--# inherit measuretypes,cartesian,clock,systemtypes;
package Flying_Object is
   type Entity is private;
   Null_Entity : constant Entity;

   procedure Create(P : in Cartesian.Position;
                    V : in Cartesian.Velocity;
                    A : in Cartesian.Accel;
                    E : out Entity);
   --# global in out clock.time;
   --# derives E from P, V, A, clock.time &
   --#  clock.time from *;

   procedure Set_Position(P : in Cartesian.Position;
                          E : in out Entity);
   --# global in out clock.time;
   --# derives E from *, P, clock.time &
   --#   clock.time from *;

   procedure Get_Position(E : in Entity;
                          P : out Cartesian.Position);
   --# global in out clock.time;
   --# derives P from E, clock.time &
   --#   clock.time from *;

   procedure Set_Velocity(V : in Cartesian.Velocity;
                          E : in out Entity);
   --# global in out clock.time;
   --# derives E from *, V, clock.time &
   --#   clock.time from *;

   procedure Get_Velocity(E : in Entity;
                          V  : out Cartesian.Velocity);
   --# global in out clock.time;
   --# derives V from E, clock.time &
   --#         clock.time from *;

   procedure Set_accel(A : in Cartesian.Accel;
                       E : in out Entity);
   --# global in out clock.time;
   --# derives E from *, A, clock.time &
   --#   clock.time from *;

   procedure Get_accel(E : in Entity;
                       A  : out Cartesian.accel);
   --# derives A from E;

private
   type Entity is record
      P : Cartesian.Position;
      V : Cartesian.Velocity;
      A : Cartesian.Accel;
      T : Clock.Millisecond;
   end record;

   Null_Entity : constant Entity :=
     Entity'(P => Cartesian.Zero_Position,
             V => Cartesian.Zero_Velocity,
             A => Cartesian.Zero_Accel,
             T => 0);

end Flying_Object;



