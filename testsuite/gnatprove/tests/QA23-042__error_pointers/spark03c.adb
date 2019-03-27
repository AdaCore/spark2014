with Ada.Text_IO;
use Ada.Text_IO;

package body Spark03c is

   protected body AA is
      entry Insert (An_Item : AI) when True is
      begin
         S := An_Item;
      end Insert;
      entry Remove (An_Item : out AI) when True is
      begin
         An_Item := S;
         --ERROR : CANNOT MOVE BORROWED VARIABLE
      end Remove;
   end AA;

   procedure Test is
   begin
      Put_Line ("X = " & Integer'Image(X) );
      Y.all := 43;
      Put_Line ("X = " & Integer'Image(X) );
      A.Insert(Y); -- move Y, RW borrow A
      --

      A.Remove(W); -- RW borrow A, get W (out parameter)
      A.Remove(Z); -- RW borrow A, get Z (out parameter)
      Z.all := 40;
      Put_Line ("X = " & Integer'Image(X) );
      W.all := 41;
      Put_Line ("X = " & Integer'Image(X) );
   end Test;

end Spark03c;
