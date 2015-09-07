pragma SPARK_Mode (On);
package Raster_Graphics is

   Workspace_Size : constant := 100;
   type Coordinate_Type is new Integer range 1 .. Workspace_Size;
   type Point is
      record
         X, Y : Coordinate_Type;
      end record;

   type Line_Algorithm_Type is (Bresenham, Xiaolin_Wu);
   type Status_Type is (Success, Line_Too_Short, Algorithm_Not_Implemented);

   Status         : Status_Type;
   Line_Algorithm : Line_Algorithm_Type;
   Line_Count     : Natural;

   procedure Draw_Line (A, B : in Point)
     with
       Global => (Input  => Line_Algorithm,
                  Output => Status,
                  In_Out => Line_Count);

end Raster_Graphics;
