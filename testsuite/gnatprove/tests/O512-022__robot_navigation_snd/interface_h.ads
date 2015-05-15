pragma Ada_2005;
pragma Style_Checks (Off);

with Interfaces.C; use Interfaces.C;
with System;

package interface_h is

   type proxy_c is record
      robot_radius : aliased double;  -- interface.h:7
      min_gap_width : aliased double;  -- interface.h:8
      obstacle_avoid_dist : aliased double;  -- interface.h:9
      max_speed : aliased double;  -- interface.h:10
      max_turn_rate : aliased double;  -- interface.h:11
      goal_position_tol : aliased double;  -- interface.h:12
      goal_angle_tol : aliased double;  -- interface.h:13
      goalX : aliased double;  -- interface.h:14
      goalY : aliased double;  -- interface.h:14
      goalA : aliased double;  -- interface.h:14
      robot_proxy_ptr : System.Address;  -- interface.h:16
      getScanCount : access function (arg1 : System.Address) return unsigned;  -- interface.h:18
      getScanRes : access function (arg1 : System.Address) return double;  -- interface.h:18
      getMaxRange : access function (arg1 : System.Address) return double;  -- interface.h:19
      getRange : access function (arg1 : System.Address; arg2 : unsigned) return double;  -- interface.h:20
      getXPos : access function (arg1 : System.Address) return double;  -- interface.h:21
      getYPos : access function (arg1 : System.Address) return double;  -- interface.h:22
      getYaw : access function (arg1 : System.Address) return double;  -- interface.h:23
      isNewGoalData : access function (arg1 : System.Address) return int;  -- interface.h:25
      PeekInputData : access function (arg1 : System.Address) return int;  -- interface.h:26
      setSpeed : access procedure
           (arg1 : System.Address;
            arg2 : double;
            arg3 : double);  -- interface.h:27
      goalReached : access procedure (arg1 : System.Address);  -- interface.h:28
   end record;
   pragma Convention (C_Pass_By_Copy, proxy_c);  -- interface.h:6

   --  procedure step_c (arg1 : access proxy_c);  -- interface.h:32
   --  pragma Import (C, step_c, "step_c");

end interface_h;
