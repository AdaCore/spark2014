with Ada.Text_IO;
use Ada.Text_IO;

package Spark03 is
   type AI is access Integer;
   protected type AA is
      entry Insert (An_Item : in out AI) with
      Depends => (An_Item => null, AA =>+ An_Item);
      entry Remove (An_Item : out AI) with
      Depends => (An_Item => AA, AA => null);
   private
      S:AI;
   end AA;

   X : aliased Integer := 42;
   Y : AI := new Integer'(X);
   Z : AI;
   W : AI;
   A : AA;

   procedure Test with Global => (In_Out => (A,Y), Output => (Z,W));

end Spark03;
