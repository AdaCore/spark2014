with Ada.Text_IO;  use Ada.Text_IO;
procedure Operator_Overload is

   type Point is    -- Cartesian coordinates of a point
      record
         X_Coord : Float;
         Y_Coord : Float;
      end record;

   function "<=" (Left : in Point; Right : in Point) return Boolean is
      -- Returns True when Left is the same distance from
      -- or closer to the origin than Right
      Left_Squared  : Float;
      Right_Squared : Float;
   begin
      Left_Squared  := Left.X_Coord  ** 2 + Left.Y_Coord  ** 2;
      Right_Squared := Right.X_Coord ** 2 + Right.Y_Coord ** 2;
      return Left_Squared <= Right_Squared;  -- Calls <= for Float numbers
   end "<=";

   P1 : Point;
   P2 : Point;

begin

   P1 := (12.4, 19.6);
   P2 := (4.3, 21.9);

   -- Function called as an infix operator
   if P1 <= P2 then
      Put_Line ("P1 is not further from the origin than P2");
   else
      Put_Line ("P1 is further from the origin than P2");
   end if;

   -- "Normal" function call
   if "<=" (P1, P2) then
      Put_Line ("P1 is not further from the origin than P2");
   else
      Put_Line ("P1 is further from the origin than P2");
   end if;

end Operator_Overload;
