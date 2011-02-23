with Bot;
package body Top is
   type Smaller is new Bot.MySmall range 1 .. 10;
   procedure A (X : MyInt)
   is
   begin
      null;
   end A;
end Top;
