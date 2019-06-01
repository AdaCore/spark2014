pragma SPARK_Mode;
with Dimensions;

package Current_Position is
   use Dimensions;

   protected type Protected_Instance_Type is

      function Get return Pose_Type with global => null;

   private
      Pose           : Dimensions.Pose_Type := ((0.0 * m, 0.0 * m), 0.0);
   end Protected_Instance_Type;

   Instance : Protected_Instance_Type;

end Current_Position;
