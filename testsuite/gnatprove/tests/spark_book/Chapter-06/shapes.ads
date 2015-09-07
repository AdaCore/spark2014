pragma SPARK_Mode(On);
package Shapes is

   subtype Coordinate_Type is Integer range -100 .. +100;
   subtype Radius_Type     is Coordinate_Type range 0 .. 10;

   type Circle is
      record
         Center_X : Coordinate_Type;
         Center_Y : Coordinate_Type;
         Radius   : Radius_Type;
      end record;

   -- Return True if X, Y are inside circle C.
   function Inside_Circle (X, Y : in Coordinate_Type;
                           C    : in Circle)  return Boolean
     with
       Pre => C.Center_X + C.Radius in Coordinate_Type and
              C.Center_X - C.Radius in Coordinate_Type and
              C.Center_Y + C.Radius in Coordinate_Type and
              C.Center_Y - C.Radius in Coordinate_Type;
end Shapes;
