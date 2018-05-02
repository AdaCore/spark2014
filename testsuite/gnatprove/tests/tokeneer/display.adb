
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
     CommonTypes,
     Display.Interfac;

use type CommonTypes.Unsigned32T;

package body Display
  with Refined_State => (State  => (CurrentDisplay,
                                    CurrentlyDisplayed,
                                    Sizes),
                         Output => Display.Interfac.Output)
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
      Top    : CommonTypes.Unsigned32T;
      Bottom : CommonTypes.Unsigned32T;
   end record;


   ------------------------------------------------------------------
   -- State
   ------------------------------------------------------------------
   CurrentDisplay     : MsgT;
   CurrentlyDisplayed : MsgT;
   Sizes              : SizesT;


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
   function CombineLines (TheMsg : MsgStrT) return ScrollStrT
   is
      Result : ScrollStrT :=
        ScrollStrT'(Text => ScrollTextT'(others => ' '),
                    Len  => 0);
   begin

      -- Add the top text...
      for I in ScrollTextI range 1..TheMsg.Top.Len loop
         pragma Loop_Invariant (1 <= I and
                                I <= TheMsg.Top.Len and
                                TheMsg = TheMsg'Loop_Entry);
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
         pragma Loop_Invariant (1 <= I and
                                I <= TheMsg.Bottom.Len and
                                TheMsg = TheMsg'Loop_Entry and
                                Result.Len = TheMsg.Top.Len + 3);
         Result.Text(Result.Len + I) := TheMsg.Bottom.Text(I);
      end loop;
      --  Assignment not used in call inlined inside SetValue
      pragma Warnings (Off, "unused assignment");
      Result.Len := Result.Len + TheMsg.Bottom.Len;
      pragma Warnings (On, "unused assignment");

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
   procedure SetValue (Msg : in     MsgT)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         CurrentDisplay)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentDisplay,
                                                       Msg),
                              CurrentDisplay       => Msg)
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
   procedure ChangeDoorUnlockedMsg (Msg : in     MsgT)
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         CurrentDisplay)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentDisplay,
                                                       Msg),
                              CurrentDisplay       =>+ Msg)
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
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State,
                                         CurrentDisplay,
                                         Sizes),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         CurrentlyDisplayed,
                                         Interfac.Output)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       CurrentDisplay,
                                                       CurrentlyDisplayed,
                                                       Sizes),
                              CurrentlyDisplayed   =>+ CurrentDisplay,
                              Interfac.Output      =>+ (CurrentDisplay,
                                                        CurrentlyDisplayed,
                                                        Sizes))
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
         -- This is seen as having no effect due to the modeling of
         -- the output of the display.
         pragma Warnings (GNATprove, Off, "statement has no effect");
         Interfac.Reset;
         pragma Warnings (GNATprove, On, "statement has no effect");

         if CommonTypes.Unsigned32T(TheMsg.Top.Len) <= Sizes.Top and
           CommonTypes.Unsigned32T(TheMsg.Bottom.Len) <= Sizes.Bottom
         then

            -- Top and Bottom text fit --> Write Top, Bottom
            Interfac.SetTopText(TopText => TheMsg.Top,
                                Written => TopWritten);
            Interfac.SetBottomText(BottomText => TheMsg.Bottom,
                                   Written    => BottomWritten);
            Written := TopWritten and BottomWritten;

         else

            -- Top or Bottom text doesn't fit --> Scroll Top+Bottom
            Interfac.SetTopTextScrollable(ScrollText => CombineLines(TheMsg),
                                          Written    => Written);

         end if;

         if not Written then
            AuditLog.AddElementToLog
              (ElementID   => AuditTypes.SystemFault,
               Severity    => AuditTypes.Warning,
               User        => AuditTypes.NoUser,
               Description => "Could not update Display");
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
   procedure Init (IsEnrolled : in     Boolean)
     with Refined_Global  => (Output => (CurrentDisplay,
                                         CurrentlyDisplayed,
                                         Sizes)),
          Refined_Depends => ((CurrentDisplay,
                               CurrentlyDisplayed) => IsEnrolled,
                              Sizes                => null)
   is
   begin
      Sizes := SizesT'(Top    => Interfac.GetMaxTextSizeTop,
                       Bottom => Interfac.GetMaxTextSizeBottom);
      if IsEnrolled then
         CurrentDisplay     := Welcome;
         CurrentlyDisplayed := Blank;
      else
         CurrentDisplay     := Blank;
         CurrentlyDisplayed := Welcome;
      end if;
   end Init;

end Display;
