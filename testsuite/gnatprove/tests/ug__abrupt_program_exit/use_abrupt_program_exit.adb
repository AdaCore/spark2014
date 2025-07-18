with Ada.Text_IO;

package body Use_Abrupt_Program_Exit with SPARK_Mode is

   procedure Get_Digit (X : out Integer) is
      S    : String (1 .. 2) with Relaxed_Initialization;
      Last : Natural;
   begin
      Ada.Text_IO.Get_Line (S, Last);
      if Last = 1 and then S (1) in '0' .. '9' then
         X := Character'Pos (S (1)) - Character'Pos ('0');
      else
         Do_Exit (1, My_Error_Message'(Kind => Input_Error));
      end if;
   exception
      when Ada.Text_IO.End_Error =>
         Do_Exit (1, My_Error_Message'(Kind => Input_Error));
   end Get_Digit;

   function Add (X, Y : Integer) return Integer is
   begin
      if X + Y > 9 then
         Do_Exit (2, My_Error_Message'(Kind => Overflow_Error));
      end if;
      return X + Y;
   end Add;

   procedure Play is
      X, Y, Z : Integer;
   begin
      Ada.Text_IO.Put_Line ("Enter first digit");
      Get_Digit (X);
      Ada.Text_IO.Put_Line ("Enter second digit");
      Get_Digit (Y);

      Z := Add (X, Y);
      Ada.Text_IO.Put_Line ("Result is " & Z'Image);
   end Play;

   procedure Auto_Play is
      Z : Integer;
   begin
      Ada.Text_IO.Put_Line ("First digit is 1");
      Ada.Text_IO.Put_Line ("Second digit is 5");

      Z := Add (1, 5);
      Ada.Text_IO.Put_Line ("Result is " & Z'Image);
   end Auto_Play;

end Use_Abrupt_Program_Exit;
