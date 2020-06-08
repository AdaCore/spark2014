with Ada.Text_IO; use Ada.Text_IO;

package body Output is

   procedure pump (name : in String; amount : in Natural) is
   begin
      Put ("Pumping: ");
      Put (name);
      Put (" amount: ");
      Put (amount'Image);
      New_Line;
   end pump;

   procedure pay (amount : in Natural) is
   begin
      Put ("Amount paid: ");
      Put (amount'Image);
      New_Line;
   end pay;

end Output;
