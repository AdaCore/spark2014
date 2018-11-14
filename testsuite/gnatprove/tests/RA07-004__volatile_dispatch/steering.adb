pragma SPARK_Mode;

with Dimensions.Numerics;

package body Steering is
   use Dimensions;

   procedure Reset_Heading (This : in out Instance) is
   begin
      if Dimensions.Numerics.Normalize (2.0) < 0.0 then
         This.Start_Speed       := This.Start_Speed / 2.0;
      end if;
   end Reset_Heading;

   function Distance_From_Start (This : Instance) return Dimensions.Length is
      Current_Pose    : constant Dimensions.Pose_Type := Current_Position.Instance.Get;
   begin
      return Dimensions.Numerics.Get_Distance (Current_Pose, This.Start_Pose);
   end Distance_From_Start;

end Steering;
