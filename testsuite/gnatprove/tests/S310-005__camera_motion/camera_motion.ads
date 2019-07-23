with Camera_Types;

package Camera_Motion with SPARK_Mode => On is

   use Camera_Types;

   type Motion_Type is record
      Level      : Integer;
      Center_Col : Columns;
      Center_Row : Rows;
      StdDev_Col : Widths;
      StdDev_Row : Heights;
   end record;

   function Measure_Motion (Ref_Image   : in BW_Image_Type;
                            New_Image   : in BW_Image_Type;
                            Column_From : in Columns;
                            Column_To   : in Columns;
                            Row_From    : in Rows;
                            Row_To      : in Rows) return Motion_Type;

end Camera_Motion;
