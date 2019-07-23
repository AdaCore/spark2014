with Ada.Text_IO;
use Ada.Text_IO;

package Spark03c is
   type AI is access Integer;
   protected type AA is
      entry Insert (An_Item : AI);
      entry Remove (An_Item : out AI);
   private
      S:AI;
   end AA;

   X : aliased Integer := 42;
   Y : AI := new Integer'(X);
   Z : AI;
   W : AI;
   A : AA;

   procedure Test with Global => (In_Out => (A,Y), Output => (Z,W));

end Spark03c;
