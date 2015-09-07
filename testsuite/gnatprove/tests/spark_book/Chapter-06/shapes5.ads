pragma SPARK_Mode(On);

package Shapes5
  with Initializes => Wild_Man
is
   subtype Coordinate_Type is Integer range -100 .. +100;
   subtype Radius_Type     is Coordinate_Type range 0 .. 10;
   type Circle is private;

   -- Create a circle object.
   function Make_Circle (X, Y   : in Coordinate_Type;
                         Radius : in Radius_Type) return Circle
      with
         Post => In_Bounds (Make_Circle'Result);

   -- Return True if X, Y are inside circle C.
   function Inside_Circle (X, Y : in Coordinate_Type;
                           C    : in Circle) return Boolean
      with Pre => In_Bounds (C);

   Wild_Man : Integer := 1;

   -- Return True if C is entirely in the workspace. Strangely it depends on a global.
   function In_Bounds (C : in Circle) return Boolean
     with Global => (Input => Wild_Man);

private
   type Circle is
      record
         Center_X : Coordinate_Type;
         Center_Y : Coordinate_Type;
         Radius   : Radius_Type;
      end record;

end Shapes5;
