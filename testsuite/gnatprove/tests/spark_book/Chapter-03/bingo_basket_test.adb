with Bingo_Numbers;  use Bingo_Numbers;
with Bingo_Basket;
with Ada.Text_IO; use Ada.Text_IO;
procedure Bingo_Basket_Test is

   package Bingo_Number_IO is new Ada.Text_Io.Integer_Io (Bingo_Number);
   use Bingo_Number_IO;

   package Letter_IO is new Ada.Text_Io.Enumeration_Io (Bingo_Letter);
   use Letter_IO;

   Number : Callable_Number;
   Letter : Bingo_Letter;
begin
   Bingo_Basket.Load;
   while not Bingo_Basket.Empty loop
      Bingo_Basket.Draw (Letter => Letter,
                         Number => Number);
      Put (Letter);
      Put (Item => Number,
           Width => 3);
      New_Line;
   end loop;
end Bingo_Basket_Test;
