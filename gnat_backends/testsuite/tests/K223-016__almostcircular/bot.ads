with Top;

package Bot is
   type MySmall is new Top.MyInt range 1 .. 50;

   procedure B (X : MySmall);
end Bot;

