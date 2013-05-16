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
-- Display.Interface
--
-- Description:
--    The interface to the Display API
--
------------------------------------------------------------------
with Display,
     BasicTypes;
--# inherit Display,
--#         BasicTypes;

private package Display.Interface
--# own out Output;
is

   ------------------------------------------------------------------
   -- GetMaxTextSizeTop
   --
   -- Description:
   --    Determine size of display lines
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeTop return BasicTypes.Unsigned32T;


   ------------------------------------------------------------------
   -- GetMaxTextSizeBottom
   --
   -- Description:
   --    Determine size of display lines
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeBottom return BasicTypes.Unsigned32T;


   ------------------------------------------------------------------
   -- SetTopText
   --
   -- Description:
   --    Write TopText to the top line of the display
   --
   ------------------------------------------------------------------
   procedure SetTopText(TopText : in     Display.MsgLineT;
                        Written :    out Boolean);
   --# global out Output;
   --# derives Output,
   --#         Written from TopText;


   ------------------------------------------------------------------
   -- SetBottomText
   --
   -- Description:
   --    Write BottomText to the bottom line of the display
   --
   ------------------------------------------------------------------
   procedure SetBottomText(BottomText : in     Display.MsgLineT;
                           Written    :    out Boolean);
   --# global out Output;
   --# derives Output,
   --#         Written from BottomText;


   ------------------------------------------------------------------
   -- SetTopTextScrollable
   --
   -- Description:
   --    Writes ScrollText to the top line of the display and scrolls
   --
   ------------------------------------------------------------------
   procedure SetTopTextScrollable(ScrollText : in     Display.ScrollStrT;
                                  Written    :    out Boolean);
   --# global out Output;
   --# derives Output,
   --#         Written from ScrollText;


   ------------------------------------------------------------------
   -- Reset
   --
   -- Description:
   --    Resets the screen
   --
   ------------------------------------------------------------------
   procedure Reset;
   --# global out Output;
   --# derives Output from ;



end Display.Interface;
