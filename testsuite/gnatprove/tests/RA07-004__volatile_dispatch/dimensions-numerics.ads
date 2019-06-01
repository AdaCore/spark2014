pragma SPARK_Mode;
package Dimensions.Numerics is
   pragma Pure;

   function Get_Distance (P1, P2 : Dimensions.Pose_Type) return Dimensions.Length;

   function Normalize (Value : Dimensions.Angle) return Dimensions.Normalized_Angle;


end Dimensions.Numerics;
