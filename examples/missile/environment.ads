-- Provide an interface to creating flying objects in the simulator
-- $Log: environment.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.4  2003/08/11 19:36:24  adi
-- Added Command testpoint
--
-- Revision 1.3  2003/08/11 19:29:32  adi
-- Corrected annos for implementation
--
-- Revision 1.2  2003/08/11 19:04:16  adi
-- Adjusted for body annos
--
-- Revision 1.1  2003/08/11 18:30:43  adi
-- Initial revision
--
--
with Measuretypes,Cartesian;
--# inherit measuretypes,cartesian,systemtypes,
--#  flying_object,clock;
package Environment
  --# own state;
  --# initializes state;
is
   type Handle is limited private;

   Null_Handle : constant Handle;

   type Kind is (Aircraft, Missile, cloud);

   -- Radar cross section
   subtype Rcs is Measuretypes.Meter_2;

   procedure Add_Object(P : in Cartesian.Position;
                        V : in Cartesian.Velocity;
                        K : in Kind;
                        R : in RCS;
                        H : out Handle);
   --# global in out state, clock.time;
   --# derives state from P, V, State, K, R, clock.time &
   --#           H from State &
   --#   clock.time from *, state;

   procedure Set_Object_Position(H : in Handle;
                                 P : in Cartesian.Position);
   --# global in out state, clock.time;
   --# derives state from *, H, P, clock.time &
   --#         clock.time from *, H, state;

   procedure Get_Object_Position(H : in Handle;
                                 P : out Cartesian.Position);
   --# global in state; in out clock.time;
   --# derives P from H, state, clock.time &
   --#         clock.time from *, H, state;

   procedure Set_Object_Velocity(H : in Handle;
                                 V : in Cartesian.Velocity);
   --# global in out state, clock.time;
   --# derives state from *, H, V, clock.time &
   --#         clock.time from *, H, state;

   procedure Get_Object_Velocity(H : in Handle;
                                 V : out Cartesian.Velocity);
   --# global in state;
   --#        in out clock.time;
   --# derives v from state, H, clock.time &
   --#         clock.time from *, H, state;

   procedure Set_Object_accel(H : in Handle;
                              A : in Cartesian.Accel);
   --# global in out state, clock.time;
   --# derives state from *, H, A, clock.time &
   --#        clock.time from *, H, state;

   procedure Delete_Object(H : in Handle);
   --# global in out state;
   --# derives state from *, H;

   -- Testpoint
   procedure Command;
   --# derives;
private

   Max_Objects : constant := 20;

   type Handle is range 0..20;
   Null_Handle : constant Handle := 0;

end Environment;
