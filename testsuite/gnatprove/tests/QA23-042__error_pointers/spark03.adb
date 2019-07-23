package body Spark03 is

   protected body AA is
      entry Insert (An_Item : in out AI) when True is -- move An_Item
      begin
         S := An_Item; --move of An_Item occurs here
         An_Item := null; --assign to An_Item

      end Insert;
      entry Remove (An_Item : out AI) when True is --move An_Item
      begin
         An_Item := S; --move of S occurs here
         S:=null; --assign to S
      end Remove;
   end AA;

   procedure Test is
   begin
      Y.all := 43; --assign to (Y.all)
      A.Insert(Y); --

      A.Remove(Z);
      Z.all := 40;
      A.Remove(W);
      W.all := 41; --Runtime error : null pointer dereferencing
   end Test;
end Spark03;
