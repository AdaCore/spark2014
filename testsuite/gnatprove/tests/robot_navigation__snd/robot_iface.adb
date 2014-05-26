with interface_h;
with Interfaces.C;

with Algorithm;

package body Robot_Iface is

   use type Interfaces.C.int;

   procedure step_c (arg1 : not null access interface_h.proxy_c);
   pragma Export (CPP, step_c);

   procedure step_c (arg1 : not null access interface_h.proxy_c) is
      C : Algorithm.Controller;
   begin
      if arg1.all.PeekInputData (arg1.all.robot_proxy_ptr) = 0 or else
        arg1.all.isNewGoalData (arg1.all.robot_proxy_ptr) = 0
      then
         return;
      end if;

      C.robot.robot_radius := Float (arg1.all.robot_radius);
      C.robot.min_gap_width := Float (arg1.all.min_gap_width);
      C.robot.obstacle_avoid_dist := Float (arg1.all.obstacle_avoid_dist);
      C.robot.max_speed := Float (arg1.all.max_speed);
      C.robot.max_turn_rate := Float (arg1.all.max_turn_rate);
      C.robot.goal_position_tol := Float (arg1.all.goal_position_tol);
      C.robot.goal_angle_tol := Float (arg1.all.goal_angle_tol);
      C.robot.goalX := Float (arg1.all.goalX);
      C.robot.goalY := Float (arg1.all.goalY);
      C.robot.goalA := Float (arg1.all.goalA);

      C.robot.scan_Count := Natural (arg1.all.getScanCount (arg1.all.robot_proxy_ptr));
      C.robot.scan_Res := Float (arg1.all.getScanRes (arg1.all.robot_proxy_ptr));
      C.robot.max_Range := Float (arg1.all.getMaxRange (arg1.all.robot_proxy_ptr));

      pragma Assert (C.robot.scan_Count = Laser_Scans'Length);

      for I in Laser_Scans'Range loop
         C.robot.scans (I) := Float (
                             arg1.all.getRange (
                               arg1.all.robot_proxy_ptr,
                               Interfaces.C.unsigned (I - Laser_Scans'First))
                            );
      end loop;
      C.robot.X := Float (arg1.all.getXPos (arg1.all.robot_proxy_ptr));
      C.robot.Y := Float (arg1.all.getYPos (arg1.all.robot_proxy_ptr));
      C.robot.Yaw := Float (arg1.all.getYaw (arg1.all.robot_proxy_ptr));
      C.robot.goal_reached := False;

      --  Create, Step;
      Algorithm.Create (Robot => C.robot);
      Algorithm.Step (This => C);

      if C.robot.speed.Opt = O_SOME then
         arg1.all.setSpeed (
                       arg1.all.robot_proxy_ptr,
                       Interfaces.C.double (C.robot.speed.modulus),
                       Interfaces.C.double (C.robot.speed.angle)
                      );
      end if;

      if C.robot.goal_reached then
         arg1.all.goalReached (arg1.all.robot_proxy_ptr);
      end if;
   end step_c;

   function GetScanCount (This : Proxy) return Natural is
   begin
      return This.scan_Count;
   end GetScanCount;

   function GetRange
     (This : Proxy;
      index : Laser_Scan_ID)
      return Formal.Numerics.NonNegative_Float
   is
   begin
      return This.scans (index);
   end GetRange;

   function GetXPos (This : Proxy) return Float is
   begin
      return This.X;
   end GetXPos;

   function GetYPos (This : Proxy) return Float is
   begin
      return This.Y;
   end GetYPos;

   function GetYaw (This : Proxy) return Float is
   begin
      return This.Yaw;
   end GetYaw;

   procedure SetSpeed (This : in out Proxy; modulus, angle : Float) is
   begin
      This.speed := (Opt => O_SOME,
                     modulus => modulus,
                     angle => angle);
   end SetSpeed;

   procedure GoalReached (This : in out Proxy) is
   begin
      This.goal_reached := True;
   end GoalReached;

end Robot_Iface;
