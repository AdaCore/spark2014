pragma SPARK_Mode(On);
package Shapes2 is
   subtype Coordinate_Type is Integer range -100 .. +100;
   subtype Radius_Type     is Coordinate_Type range 0 .. 10;
   type Circle is private;

   -- Return True if X, Y are inside circle C.
   function Inside_Circle (X, Y : in Coordinate_Type;
                           C    : in Circle) return Boolean
      with Pre => In_Bounds (C);

   -- Return True if C is entirely in the workspace.
   function In_Bounds (C : in Circle) return Boolean;

private
   type Circle is
      record
         Center_X : Coordinate_Type;
         Center_Y : Coordinate_Type;
         Radius   : Radius_Type;
      end record;
end Shapes2;
