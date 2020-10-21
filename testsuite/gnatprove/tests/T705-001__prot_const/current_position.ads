pragma SPARK_Mode;
with Dimensions;

package Current_Position is
   pragma Elaborate_Body;
   use Dimensions;

   protected Instance is
      procedure Update_Offset (Offset : in     Movement_Type);

   private
      Offset_Vector       : Vector_Type := (0.0 * m, 0.0 * m);
   end Instance;

end Current_Position;
