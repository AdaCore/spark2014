package Geometry with SPARK_Mode is
   type Rectangle is private;

   function Get_Height (X : Rectangle) return Positive with
     Ghost,
     Post => Get_Height'Result <= 100;

   function Get_Width (X : Rectangle) return Positive with
     Ghost,
     Post => Get_Width'Result <= Get_Height (X);

   function Perimeter (X : Rectangle) return Positive with
     Post => Perimeter'Result = 2 * (Get_Height (X) + Get_Width (X));

   function Area (X : Rectangle) return Positive with
     Post => Area'Result = Get_Height (X) * Get_Width (X);

   function Is_Square (X : Rectangle) return Boolean with
     Post => Is_Square'Result = (Get_Height (X) = Get_Width (X));

   function "=" (X, Y : Rectangle) return Boolean with
     Post => "="'Result =
       (Get_Height (X) = Get_Height (Y) and Get_Width (X) = Get_Width (Y));
private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part", Geometry);

   subtype Small_Positive is Positive range 1 .. 100;

   type Rectangle_Base is record
      Height : Small_Positive;
      Width  : Small_Positive;
   end record with Predicate => Width <= Height;

   function My_Eq (X, Y : Rectangle_Base) return Boolean renames "=";
   --  Introduce another name to refer to the predefined equality

   type Rectangle is new Rectangle_Base;

   function Get_Height (X : Rectangle) return Positive is (X.Height);

   function Get_Width (X : Rectangle) return Positive is (X.Width);

   function Perimeter (X : Rectangle) return Positive is
     (2 * (X.Height + X.Width));

   function Area (X : Rectangle) return Positive is
     (X.Height * X.Width);

   function Is_Square (X : Rectangle) return Boolean is
     (X.Height = X.Width);

   function "=" (X, Y : Rectangle) return Boolean renames My_Eq;
   --  "=" really is the predefined equality on rectangle
end Geometry;
