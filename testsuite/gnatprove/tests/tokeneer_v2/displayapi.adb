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
-- Implementation Notes:
--    None
--
------------------------------------------------------------------
with TcpIp;
with Ada.Strings.Fixed;
with MsgProc;

package body DisplayAPI
  with SPARK_Mode => Off  --  exception handlers
is

   ------------------------------------------------------------------
   -- GetMaxTextSizeTop
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeTop return CommonTypes.Unsigned32T
   is
      InMsg       : TcpIp.MessageT;
      OutMsg      : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "display.getMaxTextSizeTop()"),
         Length => 27);
      -- Default return value. Won't raise system fault here, just
      -- set to minimum value.
      LocalReturn : CommonTypes.Unsigned32T := 20;
      CommsIsOK   : Boolean;

   begin

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is of form ('OK[:optional]', 'val')
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
         begin
            LocalReturn := CommonTypes.Unsigned32T(
                              Integer'Value(
                                  MsgProc.GetStringByPos(Msg => Msg,
                                                         Arg => 1)));
         end;
      end if;

      return LocalReturn;

   exception

      when E : others =>

          return 20;

   end GetMaxTextSizeTop;

   ------------------------------------------------------------------
   -- GetMaxTextSizeBottom
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function GetMaxTextSizeBottom return CommonTypes.Unsigned32T is
      InMsg       : TcpIp.MessageT;
      OutMsg      : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "display.getMaxTextSizeBottom()"),
         Length => 30);
      -- Default return value. Won't raise system fault here, just set
      -- to minimum value.
      LocalReturn : CommonTypes.Unsigned32T := 20;
      CommsIsOK   : Boolean;

   begin

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is of form ('OK[:optional]', 'val')
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
         begin
            LocalReturn := CommonTypes.Unsigned32T(
                              Integer'Value(
                                  MsgProc.GetStringByPos(Msg => Msg,
                                                         Arg => 1)));
         end;
      end if;

      return LocalReturn;

   exception

      when E : others =>

          return 20;

   end GetMaxTextSizeBottom;

   ------------------------------------------------------------------
   -- SetTopText
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure SetTopText (TopText : in     String;
                         Written :    out Boolean)
   is
      OutMsg      : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "display.setTopText('" & TopText & "',)"),
         Length => 23 + TopText'Length);
      InMsg       : TcpIp.MessageT;
      CommsIsOK   : Boolean;

   begin

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is of form ('OK[:optional]', 'val')
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
         begin
            Written := Boolean'Value(
                                  MsgProc.GetStringByPos(Msg => Msg,
                                                         Arg => 1));
         end;

      else
         Written := False;
      end if;

   exception

      when E : others =>

          Written := False;

   end SetTopText;

   ------------------------------------------------------------------
   -- SetBottomText
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SetBottomText (BottomText : in     String;
                            Written    :    out Boolean)
   is
      OutMsg      : constant TcpIp.MessageT :=
                     (Data   => Ada.Strings.Fixed.Overwrite(
                                    Source   => TcpIp.NullMsg.Data,
                                    Position => 1,
                                    New_Item => "display.setBottomText('" &
                                                BottomText &
                                                "',)"),
                      Length => 26 + BottomText'Length);
      InMsg       : TcpIp.MessageT;
      CommsIsOK   : Boolean;

   begin

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is of form ('OK[:optional]', 'val')
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
         begin
            Written := Boolean'Value(
                                  MsgProc.GetStringByPos(Msg => Msg,
                                                         Arg => 1));
         end;

      else
         Written := False;
      end if;

   exception

      when E : others =>

          Written := False;

   end SetBottomText;

   ------------------------------------------------------------------
   -- SetTopTextScrollable
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure SetTopTextScrollable (ScrollText : in     String;
                                   Written    :    out Boolean)
   is
      OutMsg    : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "display.setTopTextScrollable('"
              & ScrollText & "',)"),
         Length => 33 + ScrollText'Length);
      InMsg     : TcpIp.MessageT;
      CommsIsOK : Boolean;

   begin

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then
         -- InMsg.Data is of form ('OK[:optional]', 'val')
         declare Msg : String :=
                    MsgProc.GetResponseFromMsg(InMsg);
         begin
            Written := Boolean'Value(
                                  MsgProc.GetStringByPos(Msg => Msg,
                                                         Arg => 1));
         end;
      else
         Written := False;
      end if;

   exception

      when E : others =>

          Written := False;

   end SetTopTextScrollable;

   ------------------------------------------------------------------
   -- Reset
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Reset (Success :    out Boolean)
   is
      OutMsg   : constant TcpIp.MessageT :=
        (Data   => Ada.Strings.Fixed.Overwrite
           (Source   => TcpIp.NullMsg.Data,
            Position => 1,
            New_Item => "display.reset()"),
         Length => 15);

      DontCareInMsg : TcpIp.MessageT;
   begin
      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => DontCareInMsg,
                            Success  => Success);
   end Reset;

end DisplayAPI;
