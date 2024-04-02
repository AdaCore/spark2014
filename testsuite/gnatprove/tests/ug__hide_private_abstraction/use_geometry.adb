with Geometry; use Geometry;

procedure Use_Geometry (X, Y : Rectangle) with
  SPARK_Mode,
  Global => null
is
begin
   pragma Assert ((Area (X) >= 3) = (Perimeter (X) >= 8));
   pragma Assert
     (if Area (X) = Area (Y) and then Is_Square (X) and then Is_Square (Y)
      then X = Y);
end Use_Geometry;
