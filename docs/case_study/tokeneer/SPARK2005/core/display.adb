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
-- Display
--
-- Implementation Notes:
--    This package also keeps the sizes of the two lines
--    on the display. This is used to determine whether the
--    text fits on the screen or whether the text should be
--    scrolled.
--
------------------------------------------------------------------

with AuditLog,
     AuditTypes,
     BasicTypes,
     Display.Interface;

use type BasicTypes.Unsigned32T;

package body Display
--# own State  is CurrentDisplay,
--#               CurrentlyDisplayed,
--#               Sizes &
--#     Output is out Display.Interface.Output;
is

   ------------------------------------------------------------------
   -- Types
   ------------------------------------------------------------------
   type MsgToStringT is array (MsgT) of MsgStrT;

   MsgToStrings : constant MsgToStringT := MsgToStringT'(
         Blank =>
            MsgStrT'(Top    => MsgLineT'(
                                  Text => "SYSTEM NOT OPERATIONAL ",
                                  Len  => 22),
                     Bottom => BlankLine),
         Welcome =>
            MsgStrT'(Top    => MsgLineT'(
                                  Text => "WELCOME TO TIS         ",
                                  Len  => 14),
                     Bottom => MsgLineT'(
                                  Text => "ENTER TOKEN            ",
                                  Len  => 11)),
         InsertFinger =>
            MsgStrT'(Top    => MsgLineT'(
                                  Text => "AUTHENTICATING USER    ",
                                  Len  => 19),
                     Bottom => MsgLineT'(
                                  Text => "INSERT FINGER          ",
                                  Len  => 13)),
         OpenDoor =>
            MsgStrT'(Top    => BlankLine,
                     Bottom => MsgLineT'(
                                  Text => "REMOVE TOKEN AND ENTER ",
                                  Len  => 22)),
         Wait =>
            MsgStrT'(Top    => MsgLineT'(
                                  Text => "AUTHENTICATING USER    ",
                                  Len  => 19),
                     Bottom => MsgLineT'(
                                  Text => "PLEASE WAIT            ",
                                  Len  => 11)),
         RemoveToken =>
            MsgStrT'(Top    => MsgLineT'(
                                  Text => "ENTRY DENIED           ",
                                  Len  => 12),
                     Bottom => MsgLineT'(
                                  Text => "REMOVE TOKEN           ",
                                  Len  => 12)),
         TokenUpdateFailed =>
            MsgStrT'(Top    => BlankLine,
                     Bottom => MsgLineT'(
                                  Text => "TOKEN UPDATE FAILED    ",
                                  Len  => 19)),
         DoorUnlocked =>
            MsgStrT'(Top    => BlankLine,
                     Bottom => MsgLineT'(
                                  Text => "ENTER ENCLAVE          ",
                                  Len  => 13))
         );

   type SizesT is record
      Top    : BasicTypes.Unsigned32T;
      Bottom : BasicTypes.Unsigned32T;
   end record;


   ------------------------------------------------------------------
   -- State
   ------------------------------------------------------------------
   CurrentDisplay : MsgT;
   CurrentlyDisplayed : MsgT;
   Sizes : SizesT;


   ------------------------------------------------------------------
   -- Local Subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- CombineLines
   --
   -- Description:
   --    Combines the two lines of text to make a scrollable string
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function CombineLines(TheMsg : MsgStrT) return ScrollStrT
   is
      Result : ScrollStrT :=
                  ScrollStrT'(Text => ScrollTextT'(others => ' '),
                              Len  => 0);
   begin

      -- Add the top text...
      for I in ScrollTextI range 1..TheMsg.Top.Len loop
         --# assert 1 <= I and
         --#        I <= TheMsg.Top.Len and
         --#        TheMsg = TheMsg%;
         Result.Text(I) := TheMsg.Top.Text(I);
      end loop;
      Result.Len := TheMsg.Top.Len;

      -- ...and a divider...
      Result.Text(Result.Len + 1) := ' ';
      Result.Text(Result.Len + 2) := '/';
      Result.Text(Result.Len + 3) := ' ';
      Result.Len := Result.Len + 3;

      -- ...and the bottom text.
      for I in ScrollTextI range 1..TheMsg.Bottom.Len loop
         --# assert 1 <= I and
         --#        I <= TheMsg.Bottom.Len and
         --#        TheMsg = TheMsg% and
         --#        Result.Len = TheMsg.Top.Len + 3;
         Result.Text(Result.Len + I) := TheMsg.Bottom.Text(I);
      end loop;
      Result.Len := Result.Len + TheMsg.Bottom.Len;

      return Result;
   end CombineLines;


   ------------------------------------------------------------------
   -- Exported Subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- SetValue
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure SetValue(Msg : in     MsgT)
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out CurrentDisplay;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Msg,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 CurrentDisplay &
   --#         CurrentDisplay     from Msg;
   is
   begin

      if Msg /= CurrentDisplay then
         AuditLog.AddElementToLog(
                ElementID   => AuditTypes.DisplayChanged,
                Severity    => AuditTypes.Information,
                User        => AuditTypes.NoUser,
                Description => CombineLines(MsgToStrings(Msg)).Text
                );
      end if;
      CurrentDisplay := Msg;

   end SetValue;

   ------------------------------------------------------------------
   -- ChangeDoorUnlockedMsg
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure ChangeDoorUnlockedMsg(Msg : in     MsgT)
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#        in out CurrentDisplay;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Msg,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 CurrentDisplay &
   --#         CurrentDisplay     from *,
   --#                                 Msg;
   is
   begin

      if CurrentDisplay = DoorUnlocked then
         SetValue( Msg => Msg);
      end if;

   end ChangeDoorUnlockedMsg;



   ------------------------------------------------------------------
   -- UpdateDevice
   --
   -- Implemenation Notes:
   --    None
   --
   ------------------------------------------------------------------

   procedure UpdateDevice
   --# global in     Clock.Now;
   --#        in     ConfigData.State;
   --#        in     CurrentDisplay;
   --#        in     Sizes;
   --#        in out CurrentlyDisplayed;
   --#        in out AuditLog.State;
   --#        in out AuditLog.FileState;
   --#           out Interface.Output;
   --# derives AuditLog.State,
   --#         AuditLog.FileState from AuditLog.State,
   --#                                 AuditLog.FileState,
   --#                                 Clock.Now,
   --#                                 ConfigData.State,
   --#                                 CurrentlyDisplayed,
   --#                                 CurrentDisplay,
   --#                                 Sizes &
   --#         CurrentlyDisplayed from *,
   --#                                 CurrentDisplay &
   --#         Interface.Output   from CurrentDisplay,
   --#                                 CurrentlyDisplayed,
   --#                                 Sizes;
   is
      TheMsg    : MsgStrT;
      Written   : Boolean;

      TopWritten,
      BottomWritten : Boolean;

   begin
      if CurrentDisplay /= CurrentlyDisplayed then
         CurrentlyDisplayed := CurrentDisplay;

      TheMsg := MsgToStrings(CurrentDisplay);
      -- Reset the screen
      Interface.Reset;

      if BasicTypes.Unsigned32T(TheMsg.Top.Len) <= Sizes.Top and
         BasicTypes.Unsigned32T(TheMsg.Bottom.Len) <= Sizes.Bottom then

         -- Top and Bottom text fit --> Write Top, Bottom
         Interface.SetTopText(TopText => TheMsg.Top,
                              Written => TopWritten);
         Interface.SetBottomText(BottomText => TheMsg.Bottom,
                                 Written    => BottomWritten);
         Written := TopWritten and BottomWritten;

      else

         -- Top or Bottom text doesn't fit --> Scroll Top+Bottom
         Interface.SetTopTextScrollable(
            ScrollText => CombineLines(TheMsg),
            Written    => Written);

      end if;

      if not Written then
         AuditLog.AddElementToLog(
                ElementID   => AuditTypes.SystemFault,
                Severity    => AuditTypes.Warning,
                User        => AuditTypes.NoUser,
                Description => "Could not update Display"
                );
      end if;

      end if;

   end UpdateDevice;


   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    Determine the size of the display lines
   --
   ------------------------------------------------------------------

   procedure Init(IsEnrolled : in     Boolean)
   --# global    out CurrentDisplay;
   --#           out CurrentlyDisplayed;
   --#           out Sizes;
   --# derives CurrentDisplay,
   --#         CurrentlyDisplayed from IsEnrolled &
   --#         Sizes              from ;
   is
   begin
      Sizes := SizesT'(Top    => Interface.GetMaxTextSizeTop,
                       Bottom => Interface.GetMaxTextSizeBottom);
      if IsEnrolled then
         CurrentDisplay     := Welcome;
         CurrentlyDisplayed := Blank;
      else
         CurrentDisplay     := Blank;
         CurrentlyDisplayed := Welcome;
      end if;
   end Init;


end Display;
