------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2012, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Low-level console IO for testing/debugging purposes

package AIP.IO is

   procedure Put (S : String);
   procedure Put_Line (S : String);
   --  Output a line of text to the console (without/with appended newline)

   function Line_Available return Boolean;
   --  Poll input, return True if a complete input line is available

   function Get return String;
   --  Return the current input line

end AIP.IO;
