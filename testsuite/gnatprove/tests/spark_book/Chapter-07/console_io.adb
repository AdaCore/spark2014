---------------------------------------------------------------------------
-- FILE    : console_io.adb
-- SUBJECT : Implementation of the basic I/O wrapper package.
-- AUTHOR  : (C) Copyright 2014 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Ada.Text_IO;

package body Console_IO
  with SPARK_Mode => Off is

   procedure Put_Line(Text : String) is
   begin
      Ada.Text_IO.Put_Line(Text);
   end Put_Line;

end Console_IO;
