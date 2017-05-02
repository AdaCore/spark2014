------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2012-2017, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  Low-level console IO for testing/debugging purposes

package AIP.IO is

   procedure Put (S : String);
   procedure Put_Line (S : String);
   --  Output a line of text to the console (without/with appended newline)

   function Line_Available return Boolean;
   --  Poll input, return True if a complete input line is available

   Line : String (1 .. 1024);
   --  Current input line

   function Get_Last return Integer;
   --  Return the index in Line_Buffer of the last character in the current
   --  input line. Caller is responsible for copying data from the Line buffer.

end AIP.IO;
