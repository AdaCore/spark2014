

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
-- Implementation Notes:
--    None.
--
------------------------------------------------------------------
with CommonTypes;
with DisplayAPI;
with Ada.Strings;
with Ada.Strings.Fixed;

use type CommonTypes.Unsigned32T;

package body Display.Interfac
  with SPARK_Mode => Off
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- GetMaxTextSizeTop
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeTop return CommonTypes.Unsigned32T is
     (CommonTypes.Unsigned32T(DisplayAPI.GetMaxTextSizeTop));

   ------------------------------------------------------------------
   -- GetMaxTextSizeBottom
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeBottom return CommonTypes.Unsigned32T is
     (CommonTypes.Unsigned32T(DisplayAPI.GetMaxTextSizeBottom));

   ------------------------------------------------------------------
   -- SetTopText
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SetTopText(TopText : in     Display.MsgLineT;
                        Written :    out Boolean)
   is
   begin
      DisplayAPI.SetTopText(
                    TopText => TopText.Text(1..TopText.Len),
                    Written => Written);
   end SetTopText;

   ------------------------------------------------------------------
   -- SetBottomText
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SetBottomText(BottomText : in     Display.MsgLineT;
                           Written    :    out Boolean)
   is
   begin
      DisplayAPI.SetBottomText(
                    BottomText => BottomText.Text(1..BottomText.Len),
                    Written    => Written);
   end SetBottomText;

   ------------------------------------------------------------------
   -- SetTopTextScrollable
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SetTopTextScrollable(ScrollText : in     Display.ScrollStrT;
                                  Written    :    out Boolean)
   is
   begin
      DisplayAPI.SetTopTextScrollable(
                    ScrollText => ScrollText.Text(1..ScrollText.Len),
                    Written    => Written);
   end SetTopTextScrollable;

   ------------------------------------------------------------------
   -- Reset
   --
   -- Implementation Notes:
   --    Ignore the success flag - any display problems will be
   --    caught by an attempt to write to the display
   --
   ------------------------------------------------------------------
   procedure Reset
   is
      UnusedSuccess : Boolean;
   begin
      DisplayAPI.Reset(Success => UnusedSuccess);
   end Reset;

end Display.Interfac;
