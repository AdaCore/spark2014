---------------------------------------------------------------------------
-- FILE    : logger.adb
-- SUBJECT : Body of a log management package.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(Off);

with Ada.Text_IO;

package body Logger is

   procedure Write_Error(Message : in String) is
   begin
      Ada.Text_IO.Put_Line("*** ERROR: " & Message);
   end Write_Error;

end Logger;
