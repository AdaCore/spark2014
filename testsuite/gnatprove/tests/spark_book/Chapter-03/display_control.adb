with Ada.Text_IO;
with Ada.Characters.Latin_1;  -- Characters in the
                              -- ISO 8859-1 character set
package body Display_Control is

-- Assumes that the display accepts and processes American
-- National Standards Institute (ANSI) escape sequences.

   -- Code to start an ANSI control string (the Escape
   -- control character and the left bracket character)
   ANSI_Start : constant String :=
                      Ada.Characters.Latin_1.ESC & '[';

   procedure Bold_On is
   begin -- "ESC[1m" turns on Bold
      Ada.Text_IO.Put (ANSI_Start & "1m");
      -- Send any buffered characters to the display
      Ada.Text_IO.Flush;
   end Bold_On;

   procedure Blink_On is
   begin -- "ESC[5m" turns on Blink
      Ada.Text_IO.Put (ANSI_Start & "5m");
      Ada.Text_IO.Flush;
   end Blink_On;

   procedure Normal is
   begin -- "ESC[0m" turns off all attributes
      Ada.Text_IO.Put (ANSI_Start & "0m");
      Ada.Text_IO.Flush;
   end Normal;

end Display_Control;
