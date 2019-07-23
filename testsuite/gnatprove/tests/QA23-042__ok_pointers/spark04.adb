with Ada.Text_IO;
use Ada.Text_IO;

package body Spark04 is

   package body Data is
      function CreatePoint (X: AI; Y: AI) return Point --peeked X and Y
      is (X=>X.all, Y=>Y.all); --no move for X and Y : ok
   end Data;
   use Data;

   procedure Test is
   begin
      P := CreatePoint(X=>AX,Y=>AY); --peek of AX, AY

      Put_Line ("P.X =" & Integer'Image(P.X)
                & ", P.Y =" & Integer'Image(P.Y)
                & ", AX.all =" & Integer'Image(AX.all)
                & ", AY.all =" & Integer'Image(AY.all)); --DEBUG

      AY.all := 42;
      AX.all := 40;


      Put_Line ("P.X =" & Integer'Image(P.X)
                & ", P.Y =" & Integer'Image(P.Y)
                & ", AX.all =" & Integer'Image(AX.all)
                & ", AY.all =" & Integer'Image(AY.all)); --DEBUG
   end Test;

end Spark04;
