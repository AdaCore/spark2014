

------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- DisplayAPI
--
-- Description:
--    Provides the operations to send messages to the Display.
--
------------------------------------------------------------------

with CommonTypes;

package DisplayAPI is

   ------------------------------------------------------------------
   -- GetMaxTextSizeTop
   --
   -- Description:
   --    Called at TIS initialisation, to determine the size (in characters) of
   --    the top row of the display.
   --
   ------------------------------------------------------------------

   function GetMaxTextSizeTop return CommonTypes.Unsigned32T;


   ------------------------------------------------------------------
   -- GetMaxTextSizeBottom
   --
   -- Description:
   --    Called at TIS initialisation, to determine the size (in characters) of
   --    the bottom row of the display.
   --
   ------------------------------------------------------------------

   function GetMaxTextSizeBottom return CommonTypes.Unsigned32T;


   ------------------------------------------------------------------
   -- SetTopText
   --
   -- Description:
   --    Writes the supplied text to the top line of the display.
   --
   ------------------------------------------------------------------

   procedure SetTopText(TopText : in     String;
                        Written :    out Boolean);


   ------------------------------------------------------------------
   -- SetBottomText
   --
   -- Description:
   --    Writes the supplied text to the bottom line of the display.
   --
   ------------------------------------------------------------------

   procedure SetBottomText(BottomText : in     String;
                           Written    :    out Boolean);


   ------------------------------------------------------------------
   -- SetTopTextScrollable
   --
   -- Description:
   --    Used when a message is too long to be displayed statically on the top
   --    and bottom lines of the display, and scrolls the supplied text on the
   --    top line.
   --
   ------------------------------------------------------------------

   procedure SetTopTextScrollable(ScrollText : in     String;
                                  Written    :    out Boolean);


   ------------------------------------------------------------------
   -- Reset
   --
   -- Description:
   --    Clears the display.
   --
   ------------------------------------------------------------------

   procedure Reset(Success :     out Boolean);


end DisplayAPI;
