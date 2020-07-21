pragma SPARK_Mode;
with Ada.Numerics;

package body Current_Position is


   protected body Instance is

      procedure Update_Offset (Offset : in Movement_Type) is
         Actual_Offset : Movement_Type := Offset;
         Scaling_Factor : constant Mks_Type := 20.0;
      begin
         Actual_Offset.Vector.dx := Actual_Offset.Vector.dx / Scaling_Factor;
         Actual_Offset.Vector.dy := Actual_Offset.Vector.dy / Scaling_Factor;
         Offset_Vector := Actual_Offset.Vector;
      end Update_Offset;

   end Instance;


end Current_Position;
