package Geometry with SPARK_Mode is
   type Rectangle is private;

   function Perimeter (X : Rectangle) return Positive;

   function Area (X : Rectangle) return Positive;

   function Is_Square (X : Rectangle) return Boolean;
private
   subtype Small_Positive is Positive range 1 .. 100;

   type Rectangle is record
      Height : Small_Positive;
      Width  : Small_Positive;
   end record with Predicate => Width <= Height;

   function Perimeter (X : Rectangle) return Positive is
     (2 * (X.Height + X.Width));

   function Area (X : Rectangle) return Positive is
     (X.Height * X.Width);

   function Is_Square (X : Rectangle) return Boolean is
     (X.Height = X.Width);
end Geometry;
