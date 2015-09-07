---------------------------------------------------------------------------
-- FILE    : console_io.ads
-- SUBJECT : Package that wraps some basic I/O facilities.
-- AUTHOR  : (C) Copyright 2014 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------

package Console_IO
with
  SPARK_Mode => On,
  Abstract_State => IO_Subsystem,
  Initializes => IO_Subsystem
is

   -- Outputs the given text to the standard output device. A line termination character is automatically added.
   procedure Put_Line(Text : String)
     with
       Global => (In_Out => IO_Subsystem),
       Depends => (IO_Subsystem => (IO_Subsystem, Text));

end Console_IO;
