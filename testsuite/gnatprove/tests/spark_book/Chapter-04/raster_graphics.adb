pragma SPARK_Mode(On);
package body Raster_Graphics is

   procedure Draw_Line(A, B : in Point) is

      Min_Distance : constant Coordinate_Type := 2;

      -- Verify that A, B are far enough apart.
      -- Write error code to Status if not.
      procedure Check_Distance
        with
          Global => (Input  => (A, B),
                     Output => Status)
      is
         Delta_X : Coordinate_Type := abs (A.X - B.X);
         Delta_Y : Coordinate_Type := abs (A.Y - B.Y);
      begin
         if Delta_X**2 + Delta_Y**2 < Min_Distance**2 then
            Status := Line_Too_Short;
         else
            Status := Success;
         end if;
      end Check_Distance;

   begin
      Check_Distance;
      if Status = Success then
         case Line_Algorithm is
            when Bresenham =>
               -- Algorithm implementation not shown...
               Line_Count := Line_Count + 1;

            when Xiaolin_Wu =>
               Status := Algorithm_Not_Implemented;
         end case;
      end if;
   end Draw_Line;

end Raster_Graphics;
