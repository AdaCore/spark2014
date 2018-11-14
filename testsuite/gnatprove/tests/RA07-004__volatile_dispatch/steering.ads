pragma SPARK_Mode;
with Dimensions;
with Current_Position;

package Steering is

   type Instance is tagged limited private;


   procedure Reset_Heading (This : in out Instance) with Global => null, Depends => (This => This);

   function Distance_From_Start (This : Instance) return Dimensions.Length with Volatile_Function, Global => (Input => Current_Position.Instance);

private
   type Instance is tagged limited record
      Start_Pose         : Dimensions.Pose_Type;
      Start_Speed        : Dimensions.Speed;
--      Speed_SP           : Dimensions.Speed;
      Heading_SP         : Dimensions.Normalized_Angle;
   end record;

end Steering;
