pragma SPARK_Mode(On);

package body Shapes5 is

   function Make_Circle (X, Y   : Coordinate_Type;
                         Radius : Radius_Type) return Circle
     with Refined_Post =>
       (Make_Circle'Result.Center_X + Make_Circle'Result.Radius
          in Coordinate_Type and
        Make_Circle'Result.Center_X - Make_Circle'Result.Radius
          in Coordinate_Type and
        Make_Circle'Result.Center_Y + Make_Circle'Result.Radius
          in Coordinate_Type and
        Make_Circle'Result.Center_Y - Make_Circle'Result.Radius
          in Coordinate_Type)
   is
      R : Radius_Type := Radius;
   begin
      if R >= Coordinate_Type'Last - X then
         R := Coordinate_Type'Last - X;
      end if;
      if R >= X - Coordinate_Type'First then
         R := X - Coordinate_Type'First;
      end if;
      if R >= Coordinate_Type'Last - Y then
         R := Coordinate_Type'Last - Y;
      end if;
      if R >= Y - Coordinate_Type'First then
         R := Y - Coordinate_Type'First;
      end if;
      return (X, Y, R);
   end Make_Circle;


   function Inside_Circle
     (X, Y : Coordinate_Type; C : Circle) return Boolean is

      subtype Full_Width_Type is Integer range 0 .. 2*Coordinate_Type'Last;
      Delta_X : Full_Width_Type;
      Delta_Y : Full_Width_Type;
   begin
      Delta_X := Full_Width_Type(abs (X - C.Center_X));
      Delta_Y := Full_Width_Type(abs (Y - C.Center_Y));
      return Delta_X*Delta_X + Delta_Y*Delta_Y <= Full_Width_Type(C.Radius*C.Radius);
   end Inside_Circle;


   -- This weird implementation depends on a global variable.
   function In_Bounds (C : Circle) return Boolean is
   begin
      if Wild_Man <= 0 then
         return False;
      else
         return (C.Center_X + C.Radius in Coordinate_Type and
                 C.Center_X - C.Radius in Coordinate_Type and
                 C.Center_Y + C.Radius in Coordinate_Type and
                 C.Center_Y - C.Radius in Coordinate_Type);
      end if;
   end In_Bounds;

end Shapes5;
