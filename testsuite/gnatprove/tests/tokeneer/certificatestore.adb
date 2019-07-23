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
-- CertificateStore
--
-- Implementation Notes:
--    ...
--
------------------------------------------------------------------
with AuditTypes,
     AuditLog,
     CertTypes,
     File;

use type CertTypes.SerialNumberT;

package body CertificateStore
  with Refined_State => (State     => (NextSerialNumber,
                                       Overflow),
                         FileState => StoreFile)
is

   ------------------------------------------------------------------
   -- Types
   --
   ------------------------------------------------------------------
   subtype RawNextI is Positive range 1..10;
   subtype RawNextT is String(RawNextI);

   OverflowString : constant RawNextT := "OVERFLOWED";

   ------------------------------------------------------------------
   -- State
   --
   ------------------------------------------------------------------
   NextSerialNumber : CertTypes.SerialNumberT;
   Overflow         : Boolean;
   StoreFile        : File.T := File.NullFile;


   ------------------------------------------------------------------
   -- Local Subprograms
   --
   ------------------------------------------------------------------
   ------------------------------------------------------------------
   -- GetNextSerialNumber
   --
   -- Description:
   --    Attempts To read the next serial number from the Store.
   --    Success is true if the Store is 'good'.
   --    Next is set to the number read from the store, if it is
   --    valid, otherwise it is set to 'Last.
   --    OFlow is False if a valid number is read from the Store,
   --    otherwise it is True.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure GetNextSerialNumber (Next    : out CertTypes.SerialNumberT;
                                  OFlow   : out Boolean;
                                  Success : out Boolean)
     with Global  => (In_Out => StoreFile),
          Depends => ((Next,
                       OFlow,
                       StoreFile,
                       Success)   => StoreFile);

   procedure GetNextSerialNumber (Next    : out CertTypes.SerialNumberT;
                                  OFlow   : out Boolean;
                                  Success : out Boolean)
     with SPARK_Mode => Off   --  exception handler
   is
      RawNext : RawNextT;
      Stop    : Natural;

      NewNext : CertTypes.SerialNumberT;

      Opened,
      Closed  : Boolean;
      ReadOK  : Boolean := True;

      ------------------------------------------------------------------
      -- StringIsOverflowed
      --
      -- Description:
      --    Compares Text with the "OVERFLOWED" string.
      --
      -- Implementation Notes:
      --    None
      --
      ------------------------------------------------------------------
      function StringIsOverflowed(Text : RawNextT) return Boolean
      is
         Result : Boolean := True;
      begin
         for i in RawNextI loop
            if Text(i) /= OverflowString(i) then
               Result := False;
               exit;
            end if;
         end loop;

         return Result;
      end StringIsOverflowed;

      ------------------------------------------------------------------
      -- ConvertTo32
      --
      -- Description:
      --    Converts the Text string into the SerialNumber type.
      --    Ok is false if Text is not the 'Image' of a serial number.
      --
      -- Implementation Notes:
      --    Hidden due to use of the 'Value attribute
      --
      ------------------------------------------------------------------
      procedure ConvertTo32(Text   : in     RawNextT;
                            Length : in     Natural;
                            Num    :    out CertTypes.SerialNumberT;
                            Ok     :    out Boolean)
      is
      begin
         Num := CertTypes.SerialNumberT'Value(Text(1..Length));
         Ok  := True;
      exception
         when E : others =>
            Ok  := False;
            Num := CertTypes.SerialNumberT'First;
      end ConvertTo32;

   ----------------------------
   -- begin NextSerialNumber --
   ----------------------------
   begin
      OFlow := True;
      Next  := CertTypes.SerialNumberT'Last;

      File.OpenRead(TheFile => StoreFile,
                    Success => Opened);

      if Opened then
         File.GetString(TheFile => StoreFile,
                        Text    => RawNext,
                        Stop    => Stop);

         if StringIsOverflowed(RawNext) then
            OFlow   := True;
            Next    := CertTypes.SerialNumberT'Last;
         else
            ConvertTo32(Text   => RawNext,
                        Length => Stop,
                        Num    => NewNext,
                        Ok     => ReadOK);
            if ReadOK then
               OFlow := False;
               Next  := NewNext;
            end if;
         end if;
      end if;

      File.Close(StoreFile,
                 Closed);

      Success := Opened and ReadOK and Closed;

   end GetNextSerialNumber;

   ------------------------------------------------------------------
   -- PutNextSerialNumber
   --
   -- Description:
   --    Attempts to write the next serial number to the Store.
   --    Success is set to False if it cannot be written.
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure PutNextSerialNumber (Next    : in     CertTypes.SerialNumberT;
                                  OFlow   : in     Boolean;
                                  Success :    out Boolean)
     with Global  => (In_Out => StoreFile),
          Depends => ((StoreFile,
                       Success)   => (Next,
                                      OFlow,
                                      StoreFile))
   is
      RawNext : RawNextT;
      Stop    : Natural;
      Opened,
      Closed  : Boolean;

      ------------------------------------------------------------------
      -- ConvertFrom32
      --
      -- Description:
      --    Converts the SerialNumber type into a Text string.
      --
      -- Implementation Notes:
      --    Hidden due to use of the 'Image attribute
      --
      ------------------------------------------------------------------
      procedure ConvertFrom32 (Num    : in     CertTypes.SerialNumberT;
                               Text   :    out RawNextT;
                               Length :    out RawNextI)
        with Depends => ((Length,
                          Text)   => Num)
      is
         Str : String := CertTypes.SerialNumberT_Image(Num);
      begin
         pragma Assume (Str'Length <= 11);
         -- Trim the automatic space at the start of the string
         Length := Str'Length - 1;
         Text(1..Length) := Str(2..Length + 1);
         Text(Length + 1..RawNextI'Last) := (others => ' ');
      end ConvertFrom32;
      pragma Annotate (GNATprove, False_Positive, "might not be initialized",
                       "Initialization of string in two steps");

   begin
      File.OpenWrite(StoreFile, Opened);

      if Opened then

         if Oflow then
            File.PutString (TheFile => StoreFile,
                            Text    => OverflowString,
                            Stop    => 0);

         else
            ConvertFrom32(Num    => Next,
                          Text   => RawNext,
                          Length => Stop);
            File.PutString (TheFile => StoreFile,
                            Text    => RawNext,
                            Stop    => Stop);
         end if;
      end if;

      File.Close(StoreFile,
                 Closed);

      Success := Opened and Closed;
   end PutNextSerialNumber;

   ------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   --
   ------------------------------------------------------------------
   procedure Init
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              Output => (NextSerialNumber,
                                         OverFlow),
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         StoreFile)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       StoreFile),
                              (NextSerialNumber,
                               Overflow,
                               StoreFile)          => StoreFile)
   is
      ReadOK : Boolean;
   begin
      File.SetName(TheFile => StoreFile,
                   TheName => "./System/cert.dat");

      if File.Exists (TheFile => StoreFile) then
         GetNextSerialNumber(Next    => NextSerialNumber,
                             OFlow   => Overflow,
                             Success => ReadOk);

         if not ReadOK then
            AuditLog.AddElementToLog(
                  ElementID   => AuditTypes.SystemFault,
                  Severity    => AuditTypes.Warning,
                  User        => AuditTypes.NoUser,
                  Description => "Certificate Store read error"
                  );
         end if;

      else
         -- Store does not exist - set to 'First
         NextSerialNumber := CertTypes.SerialNumberT'First;
         Overflow := False;
      end if;

   end Init;

   ------------------------------------------------------------------
   -- UpdateStore
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   procedure UpdateStore
     with Refined_Global  => (Input  => (Clock.Now,
                                         ConfigData.State),
                              Output => Overflow,
                              In_Out => (AuditLog.FileState,
                                         AuditLog.State,
                                         NextSerialNumber,
                                         StoreFile)),
          Refined_Depends => ((AuditLog.FileState,
                               AuditLog.State)     => (AuditLog.FileState,
                                                       AuditLog.State,
                                                       Clock.Now,
                                                       ConfigData.State,
                                                       NextSerialNumber,
                                                       StoreFile),
                              (NextSerialNumber,
                               StoreFile)          =>+ NextSerialNumber,
                              Overflow             => NextSerialNumber)
   is
      Written : Boolean := False;
      Exists  : Boolean := True;
   begin
      if NextSerialNumber < CertTypes.SerialNumberT'Last then
         NextSerialNumber := NextSerialNumber + 1;
         Overflow := False;
      else
         Overflow := True;
      end if;

      if not File.Exists(TheFile => StoreFile) then
         File.Create(TheFile => StoreFile,
                     Success => Exists);
         if Exists then
            File.Close(TheFile => StoreFile,
                       Success => Exists);
         end if;

      end if;

      if Exists then
         PutNextSerialNumber(Next    => NextSerialNumber,
                             OFlow   => Overflow,
                             Success => Written);

      end if;

      if not (Exists and Written) then
         AuditLog.AddElementToLog
           (ElementID   => AuditTypes.SystemFault,
            Severity    => AuditTypes.Warning,
            User        => AuditTypes.NoUser,
            Description => "Certificate Store write error - " &
              "state will be lost at Power Down."
           );
      end if;

   end UpdateStore;

   ------------------------------------------------------------------
   -- SerialNumberHasOverflowed
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function SerialNumberHasOverflowed return Boolean
     with Refined_Global => Overflow
   is
   begin
      return Overflow;
   end SerialNumberHasOverflowed;

   ------------------------------------------------------------------
   -- SerialNumber
   --
   -- Implementation Notes:
   --    None
   --
   ------------------------------------------------------------------
   function SerialNumber return CertTypes.SerialNumberT
     with Refined_Global => (Input    => NextSerialNumber,
                             Proof_In => Overflow)
   is
   begin
      return NextSerialNumber;
   end SerialNumber;

end CertificateStore;
