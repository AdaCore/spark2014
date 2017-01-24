with Robot_Iface;
with Spaces.Angles;
with Spaces.Positions;

with Gaps;
with Valleys;

with Ada.Containers.Formal_Doubly_Linked_Lists;

with Formal.Numerics;

package Algorithm with
  SPARK_Mode
is

   --  pragma Pure;

   --  TODO: this type should be private (and limited).
   type Controller;

   use Spaces.Angles;
   use Spaces.Positions;
   use Gaps;

   type Option is (O_NONE, O_SOME);

   type Valley_Option (Opt : Option := O_NONE) is record
      case Opt is
         when O_NONE =>
            null;
         when O_SOME =>
            value : Valleys.Valley;
      end case;
   end record;

   Max_Gaps : constant := Robot_Iface.GetCount;

   subtype Gap_ID is Integer range 1 .. Max_Gaps;

   package Gap_Vectors is new
     Ada.Containers.Formal_Doubly_Linked_Lists (Gaps.Gap);

   subtype List is Gap_Vectors.List (Max_Gaps);

   type Laser_Scan_Data is
      record
         first : Formal.Numerics.NonNegative_Float;
         second : Angle;
      end record;

   type Laser_Scans is array (Robot_Iface.Laser_Scan_ID) of Laser_Scan_Data;

   type Controller is record
      robot : Robot_Iface.Proxy :=
         (scan_Count => 0,
          scans      => (others => 0.0),
          speed      => (Opt => Robot_Iface.O_NONE),
          goal_reached => false,
          others    => 0.0);
      laserScan : Laser_Scans :=
         ( others =>  (first => 0.0, second => Null_Angle));
      gapVec    : List;
      obsAvoidDelta : Float := 0.0;
      driveAngle : Angle := Null_Angle;
   end record;
   pragma Convention (CPP, Controller);

   function isFilterClear
     (scans         : Laser_Scans;
      testBearing   : Angle;
      width         : Float;
      forwardLength : Float;
      bDoRearCheck  : Boolean)
      return          Boolean;

   function isRisingGapSafe
     (This      : Controller;
      risingGap : Gap)
      return      Boolean;

   procedure buildGapVector (gapVec : in out List;
                             laserscan : Laser_Scans;
                             robotRadius : Formal.Numerics.Positive_Float;
                             minGapWidth : Formal.Numerics.Positive_Float;
                             fMaxRange : Formal.Numerics.Positive_Float);

   procedure removeDuplicateGaps (This : in out Controller)
   with
     Post => This.robot.robot_radius = This.robot.robot_radius'Old;

   function findBestValley
     (This       : Controller;
      distToGoal : Position)
      return Valley_Option
   with
     Pre => distToGoal /= Zero_Position;

   function ObsAvoidDelta
     (This       : Controller;
      safetyDist : Float)
      return Float
   with
     Pre => safetyDist /= 0.0;

   -- public

   procedure Create (Robot : Robot_Iface.Proxy);

   procedure Step (This : in out Controller);

end Algorithm;
