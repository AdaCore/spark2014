------------------------------------------------------------------
-- Tokeneer ID Station Core Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- Display.Interfac
--
-- Description:
--    The interface to the Display API
--
------------------------------------------------------------------
with Display,
     CommonTypes;

private package Display.Interfac
  with Abstract_State => (Output with External => Async_Readers,
                                      Part_Of  => Display.Output),
       Initializes => Output
is

   ------------------------------------------------------------------
   -- GetMaxTextSizeTop
   --
   -- Description:
   --    Determine size of display lines
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeTop return CommonTypes.Unsigned32T
     with Global => null;

   ------------------------------------------------------------------
   -- GetMaxTextSizeBottom
   --
   -- Description:
   --    Determine size of display lines
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeBottom return CommonTypes.Unsigned32T
     with Global => null;

   ------------------------------------------------------------------
   -- SetTopText
   --
   -- Description:
   --    Write TopText to the top line of the display
   --
   ------------------------------------------------------------------
   procedure SetTopText(TopText : in     Display.MsgLineT;
                        Written :    out Boolean)
     with Global  => (Output => Output),
          Depends => ((Output,
                       Written) => TopText);

   ------------------------------------------------------------------
   -- SetBottomText
   --
   -- Description:
   --    Write BottomText to the bottom line of the display
   --
   ------------------------------------------------------------------
   procedure SetBottomText(BottomText : in     Display.MsgLineT;
                           Written    :    out Boolean)
     with Global  => (Output => Output),
          Depends => ((Output,
                       Written) => BottomText);

   ------------------------------------------------------------------
   -- SetTopTextScrollable
   --
   -- Description:
   --    Writes ScrollText to the top line of the display and scrolls
   --
   ------------------------------------------------------------------
   procedure SetTopTextScrollable(ScrollText : in     Display.ScrollStrT;
                                  Written    :    out Boolean)
     with Global  => (Output => Output),
          Depends => ((Output,
                       Written) => ScrollText);

   ------------------------------------------------------------------
   -- Reset
   --
   -- Description:
   --    Resets the screen
   --
   ------------------------------------------------------------------
   procedure Reset
     with Global  => (Output => Output),
          Depends => (Output => null);

end Display.Interfac;
