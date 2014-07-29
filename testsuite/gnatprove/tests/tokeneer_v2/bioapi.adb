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
-- BioAPI
--
-- Implementation Notes:
--    This API has been modeled on the BioAPI specification.
--
------------------------------------------------------------------

with Ada.Strings.Fixed,
     Ada.Text_IO,
     MsgProc,
     TcpIp,
     Unchecked_Conversion;

package body BioAPI
  with SPARK_Mode => Off  --  exception handlers
is

   ------------------------------------------------------------------
   --
   -- Types
   --
   ------------------------------------------------------------------

   -- ReturnT models the possible errors that could be raised
   -- performing library actions.

   type ReturnT is
      (BioApiOk,
       -- High Level framework errors:
       InternalError,
       MemoryError,
       FunctionFailed,
       InvalidData,
       BioApiNotInitialized,
       ModuleLoadFailed,
       ModuleUnloadFailed,
       -- BSP Level errors:
       BspInternalError,
       BspMemoryError,
       BspFunctionFailed,
       BspInvalidData,
       BspUnableToCapture,
       BspTimeoutExpired,
       BspBirSignatureFailure,
       BspInconsistentPurpose,
       -- Device Level Errors:
       DeviceLevelError);

   for ReturnT use   -- Error codes Values.
      (BioApiOk                => 16#0000#,
       InternalError           => 16#0001#,
       MemoryError             => 16#0002#,
       FunctionFailed          => 16#000A#,
       InvalidData             => 16#0046#,
       BioApiNotInitialized    => 16#0102#,
        ModuleLoadFailed       => 16#0116#,
       ModuleUnloadFailed      => 16#0118#,
       BspInternalError        => 16#1001#,
       BspMemoryError          => 16#1002#,
        BspFunctionFailed      => 16#100A#,
        BspInvalidData         => 16#1046#,
       BspUnableToCapture      => 16#1101#,
        BspTimeoutExpired      => 16#1103#,
        BspBirSignatureFailure => 16#1105#,
       BspInconsistentPurpose  => 16#110D#,
       DeviceLevelError        => 16#2001#);

   for ReturnT'Size use 32;

   ------------------------------------------------------------------
   -- Local Subprograms
   ------------------------------------------------------------------

   ------------------------------------------------------------------
   -- CodeToValue
   --
   -- Description:
   --    Unchecked conversion from ReturnT to its numeric rep.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   function CodeToValue is new
      Unchecked_Conversion (Source => ReturnT,
                            Target => CommonTypes.Unsigned32T);


   ------------------------------------------------------------------
   -- Exported subprograms
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- SamplePresent
   --
   -- Implementation Notes:
   --    Return false if there are any problems with communication.
   --
   ------------------------------------------------------------------
   function SamplePresent return Boolean
   is
      InMsg     : TcpIp.MessageT;
      OutMsg    : constant TcpIp.MessageT :=
                     (Data   => Ada.Strings.Fixed.Overwrite(
                                      Source   => TcpIp.NullMsg.Data,
                                      Position => 1,
                                      New_Item => "bioDevice.imageReady()"),
                      Length => 22);
      CommsIsOK : Boolean;

   begin

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => OutMsg,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      return Boolean'Value(MsgProc.GetStringByPos(
                              Msg => MsgProc.GetResponseFromMsg(InMsg),
                              Arg => 1))
             and CommsIsOK;

   exception

      when E : others =>

          return False;

   end SamplePresent;

   ------------------------------------------------------------------
   -- Verify
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Verify (Template       : in     TemplateT;
                     MaxFAR         : in     RateT;
                     Matched        :    out Boolean;
                     FARAchieved    :    out RateT;
                     BioReturn      :    out CommonTypes.Unsigned32T)
   is
      TemplateString : String := Ada.Strings.Fixed.Trim(
                                        Template.ID,
                                        Ada.Strings.Both);
      MaxFARString : String := Ada.Strings.Fixed.Trim(
                                        RateT'Image(MaxFAR),
                                        Ada.Strings.Both);

      DoVerify : constant TcpIp.MessageT :=
                     (Data   => Ada.Strings.Fixed.Overwrite(
                                      Source   => TcpIp.NullMsg.Data,
                                      Position => 1,
                                      New_Item => "bioDevice.verify('" &
                                                  TemplateString &
                                                  "', '" &
                                                  MaxFARString &
                                                  "')"),
                      Length => 24 +
                                TemplateString'Length +
                                MaxFARString'Length);

      InMsg     : TcpIp.MessageT;
      CommsIsOK : Boolean;

   begin
      -- Default values
      -- Very, very bad attempted match...
      FARAchieved := RateT'Last;
      Matched     := False;
      BioReturn   := CodeToValue(BioApiOk);

      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => DoVerify,
                            Incoming => InMsg,
                            Success  => CommsIsOK);

      if CommsIsOK then

         Matched  := Boolean'Value(
                        MsgProc.GetStringByPos(
                           Msg => MsgProc.GetResponseFromMsg(InMsg),
                           Arg => 1));

         -- AchievedFAR
         FARAchieved := RateT'Value(
                           MsgProc.GetStringByPos(
                              Msg => MsgProc.GetResponseFromMsg(InMsg),
                              Arg => 2));
      else
         -- Communication failure with the BSP
         BioReturn := CodeToValue(BspFunctionFailed);

      end if;

   exception

      when E : others =>

         -- Very, very bad attempted match...
         FARAchieved := RateT'Last;
         Matched     := False;
         -- Exception caused by invalid data
         BioReturn   := CodeToValue(InvalidData);

   end Verify;

   ------------------------------------------------------------------
   -- Reset
   --
   -- Implementation Notes:
   --    A failure does not raise a system fault
   --
   ------------------------------------------------------------------
   procedure Reset
   is
      DoReset : constant TcpIp.MessageT :=
                     (Data   => Ada.Strings.Fixed.Overwrite(
                                      Source   => TcpIp.NullMsg.Data,
                                      Position => 1,
                                      New_Item => "bioDevice.reset()"),
                      Length => 17);

      DontCareInMsg : TcpIp.MessageT;
      DontCareIsOK  : Boolean;
   begin
      TcpIp.SendAndReceive (IsAdmin  => False,
                            Outgoing => DoReset,
                            Incoming => DontCareInMsg,
                            Success  => DontCareIsOK);
   end Reset;

end BioAPI;
