with Ada.Text_IO;
use Ada.Text_IO;


procedure Spark03b is
   type AI is access all Integer;
   protected type AA is
      entry Insert (An_Item : in out AI) with
      Depends => (AA => null, S => AA),
        Global => S;
      entry Remove (An_Item : out AI);
   private
      S:AI;
   end AA;

   protected body AA is
      entry Insert (An_Item : in out AI) when True is -- move An_Item
      begin
         S := An_Item;
      end Insert;
      entry Remove (An_Item : out AI) when True is
      begin
         An_Item := S;
      end Remove;
   end AA;
   X : aliased Integer := 42;
   Y : AI := X'Access; --move of Y occurs here
   Z : AI;
   W : AI;
   A : AA;
begin
   Put_Line ("X = " & Integer'Image(X) );
   Y.all := 43; --assign to (Y.all)
   Put_Line ("X = " & Integer'Image(X) );
   A.Insert(Y); --


   A.Remove(W);
   A.Remove(Z);
   Z.all := 40;
   Put_Line ("X = " & Integer'Image(X) );
   W.all := 41;
   Put_Line ("X = " & Integer'Image(X) );
end Spark03b;
