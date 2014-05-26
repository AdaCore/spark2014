with Formal.Numerics;

package Robot_Iface is

   --  Fix the number of laser rays.
   GetCount : constant Natural := 1000;

   subtype Laser_Scan_ID is Integer range 1 .. GetCount;

   type Laser_Scans is array (Laser_Scan_ID) of Formal.Numerics.NonNegative_Float;

   type Option is (O_NONE, O_SOME);

   type Speed_Option (Opt : Option := O_NONE) is record
      case Opt is
         when O_NONE =>
            null;
         when O_SOME =>
            modulus, angle : Float;
      end case;
   end record;

   --  TODO: this type should be private and limited.
   type Proxy is
      record
         robot_radius : Formal.Numerics.Positive_Float;
         min_gap_width : Formal.Numerics.Positive_Float;
         obstacle_avoid_dist : Formal.Numerics.Positive_Float;
         max_speed : Formal.Numerics.Positive_Float;
         max_turn_rate : Formal.Numerics.Positive_Float;
         goal_position_tol : Formal.Numerics.NonNegative_Float;
         goal_angle_tol : Formal.Numerics.NonNegative_Float;
         goalX, goalY, goalA : Float;
         scan_Count : Natural;
         scan_Res : Formal.Numerics.Positive_Float;
         max_Range : Formal.Numerics.Positive_Float;
         scans : Laser_Scans;
         X, Y, Yaw : Formal.Numerics.Unbounded_Float;
         speed : Speed_Option;
         goal_reached : Boolean;
      end record;

   function GetScanCount (This : Proxy) return Natural;

   function GetRange (This : Proxy; index : Laser_Scan_ID) return Formal.Numerics.NonNegative_Float;
   function GetXPos (This : Proxy) return Float;
   function GetYPos (This : Proxy) return Float;
   function GetYaw (This : Proxy) return Float;

--     function isNewGoalData (This : Proxy) return Boolean;
--     function PeekInputData(This : Proxy) return Boolean;

   procedure SetSpeed (This : in out Proxy; modulus, angle : Float);
   procedure GoalReached (This : in out Proxy);

end Robot_Iface;
