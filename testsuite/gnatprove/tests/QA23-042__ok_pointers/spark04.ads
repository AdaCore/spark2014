with Ada.Text_IO;
use Ada.Text_IO;

package Spark04 is

   package Data is
      type Point is record
         X,Y : aliased Integer;
      end record;
      type AI is access Integer;
      function CreatePoint(X: AI; Y: AI) return Point;
   end Data;
   use Data;

   X : aliased Integer := 10;
   Y : aliased Integer := 14;
   AX : AI := new Integer'(X);
   AY : AI := new Integer'(Y);
   P : Point;

   procedure Test with
     Global => (In_Out  => (AX, AY, Ada.Text_IO.File_System),
                 Output => P);

end Spark04;
