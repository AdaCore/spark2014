
package body Challenges with SPARK_Mode => On is
   use Dimensions;


   function Get_Distance (V : Dimensions.Vector_Type) return Dimensions.Non_Negative_Length is
   begin
      return Dimensions.Mks_Numerics.Sqrt (Area'(V.dx**2) + Area'(V.dy**2));
   end Get_Distance;

   function Get_Distance (P1, P2 : Dimensions.Position_Type) return Dimensions.Non_Negative_Length is
      dX : constant Dimensions.Length := (P2.X - P1.X);
      dY : constant Dimensions.Length := (P2.Y - P1.Y);
   begin
      return Get_Distance ((dx => dX,
                            dy => dY));
   end Get_Distance;


   function Get_Remaining_Distance (Start_Pose      : Pose_Type;
                                    Target_Position : Position_Type;
                                    Distance        : Short_Length) return Short_Length is
   begin
      return Get_Distance (Start_Pose.Pos, Target_Position) - Distance;
   end Get_Remaining_Distance;

   procedure Go_To_Position_Distance (Position : Dimensions.Position_Type;
                                      Distance : Short_Length) is
      Start_Pose : constant Dimensions.Pose_Type := ((0.0 * m, 0.0 * m), 0.0);
      Remaining_Distance : Dimensions.Short_Length := 0.0 * m;
      pragma Unreferenced (Remaining_Distance);
   begin
      Remaining_Distance := Get_Remaining_Distance (Start_Pose, Position, Distance);
   end Go_To_Position_Distance;

   procedure Calibrate_At_Junction_Or_Line_End (Pose : Pose_Type) is
   begin
         Go_To_Position_Distance (Position => Pose.Pos, Distance => 60.0 * cm);
   end Calibrate_At_Junction_Or_Line_End;


end Challenges;
