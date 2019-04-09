package body Spark03b is

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

   procedure Test is
   begin
      Y.all := 43; --assign to (Y.all)
      A.Insert(Y); --

      A.Remove(W);
      A.Remove(Z);
      Z.all := 40;
      W.all := 41;
   end Test;

end Spark03b;
