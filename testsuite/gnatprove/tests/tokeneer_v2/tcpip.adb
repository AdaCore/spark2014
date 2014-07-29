------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

with Ada.Text_IO;
with Ada.Strings.Fixed;
with GNAT.Sockets;
with MsgProc;
with Ada.Command_Line;

use type GNAT.Sockets.Selector_Status;

package body TcpIp
  with SPARK_Mode => Off  --  exception handlers
is

   --
   -- Current SPRE information...
   --
   PortalPort : GNAT.Sockets.Port_Type := 12001;
   AdminPort  : GNAT.Sockets.Port_Type := 12000;

   type SPREMachineT is
   record
     Data   : String(1 .. 30);
     Length : Natural range 0 .. 30;
   end record;

   SPREMachine : SPREMachineT :=
     (Data => "                              ",
      Length => 20);

   -- Enumeration of the currently available servers
   type ServerT is (Admin,Portal);

   --
   -- PortTo:
   --
   --    Used internally to keep track of the state of
   --    each of the available SPRE device driver server ports.
   --

   type PortStateT is (Connected, NotConnected);

   -- Are we connected to the port? if so, which socket and channel?
   type PortInfoT is record
      State   : PortStateT;
      Socket  : GNAT.Sockets.Socket_Type;
      Channel : GNAT.Sockets.Stream_Access;
   end record;

   type ConnectStateT is array (ServerT) of PortInfoT;
   PortTo : ConnectStateT := (others  =>
                                 (State   => NotConnected,
                                  Socket  => GNAT.Sockets.No_Socket,
                                  Channel => GNAT.Sockets.Stream(
                                                 GNAT.Sockets.No_Socket) ));

   -- Has the socket library been initialized?
   type WinSockStateT is (Uninitialized, Initialized);
   WinSockState : WinSockStateT := Uninitialized;


   -- Once a socket is open, can use GNAT.Sockets.Check_Selector to
   -- monitor changes in state of a set of sockets. ReadSet and WriteSet
   -- represent the two sets of sockets that will be maintained.

   ReadSet      : GNAT.Sockets.Socket_Set_Type;
   WriteSet     : GNAT.Sockets.Socket_Set_Type;
   CheckStatus  : GNAT.Sockets.Selector_Status;
   CheckTimeout : constant Duration := 5.0;
   Selector     : GNAT.Sockets.Selector_Type;

   --------------------------------------------------------------------
   --
   -- Local Subprograms
   --
   --------------------------------------------------------------------

   --------------------------------------------------------------------
   -- StartDebug
   --
   -- Description:
   --   Starts a TCPIP log file.
   --
   -- Implementation Notes:
   --    Set to Null in delivered system.
   --
   --------------------------------------------------------------------
   procedure StartDebug
   is
      --      MyError : Ada.Text_IO.File_Type;

   begin
      null;

      --      Ada.Text_IO.Create(File => MyError,
      --                         Mode => Ada.Text_IO.Out_File,
      --                         Name => "TCPIP.Log");
      --      Ada.Text_Io.Close(MyError);
   end StartDebug;

   --------------------------------------------------------------------
   -- DebugOutput
   --
   -- Description:
   --   Writes a debug message to the TCPIP log file.
   --
   -- Implementation Notes:
   --    Set to Null in delivered system.
   --
   --------------------------------------------------------------------
   procedure DebugOutput(Text : String)
   is
      --      MyError : Ada.Text_IO.File_Type;

   begin

      null;
      --         Ada.Text_IO.Open(File => MyError,
      --                          Mode => Ada.Text_IO.Append_File,
      --                          Name => "TCPIP.Log");
      --         Ada.Text_IO.Put_Line(File => MyError,
      --                              Item => Text);
      --         Ada.Text_IO.Close(MyError);
   end DebugOutput;

   --------------------------------------------------------------------
   -- MsgToRead
   --
   -- Description:
   --    Checks whether there is a message waiting to be read from a socket.
   --
   -- Implementation Notes:
   --    Adds socket to ReadSet, so shouldn't really be a function...
   --
   --------------------------------------------------------------------
   function MsgToRead (Server : in ServerT) return Boolean is
      LocalReturn : Boolean := False;
   begin

      -- Add socket to the ReadSet, and check for a message
      -- from the Server.
      GNAT.Sockets.Set ( Item   => ReadSet,
                         Socket => PortTo(Server).Socket );

      GNAT.Sockets.Check_Selector ( Selector     => Selector,
                                    R_Socket_Set => ReadSet,
                                    W_Socket_Set => WriteSet,
                                    Status       => CheckStatus,
                                    Timeout      => CheckTimeout );

      if CheckStatus = GNAT.Sockets.Completed and then
         GNAT.Sockets.Is_Set( Item   => ReadSet,
                              Socket => PortTo(Server).Socket ) then

         LocalReturn := True;

      -- For debugging...
      else
         DebugOutput("Data not available to read");
      end if;

      return LocalReturn;

   end MsgToRead;

   --------------------------------------------------------------------
   -- ReadMsg
   --
   -- Description:
   --    Reads message from Server, terminating on reading the message
   --    delineation sequence (CR,LF). The Length field does not include
   --    the delineation sequence i.e. only length of actual message data.
   --
   -- Implementation Notes:
   --    There may well be more data to read. This will be 'cleared' when
   --    we next attempt to SendMsg.
   --
   --------------------------------------------------------------------
   procedure ReadMsg (Server  : in     ServerT;
                      Msg     :    out MessageT;
                      Success :    out Boolean)
   is
   begin
      Success := True;

      for i in MessageIndexT'Range loop

         Character'Read ( PortTo(Server).Channel,
                          Msg.Data(i) );

         if Msg.Data(i)     = ASCII.Lf and then
            Msg.Data(i - 1) = ASCII.Cr then

            Msg.Data(i - 1 .. i) := (others => ASCII.Nul);
            Msg.Length := i - 2;
            exit;

         end if;

      end loop;

      -- For debugging...
      DebugOutput("Rcvd: " & Msg.Data(1..Msg.Length));

   exception
      when E : others =>
         Success := False;
         DebugOutput("Read Error.");
   end ReadMsg;

   --------------------------------------------------------------------
   -- SendMsg
   --
   -- Description:
   --    Sends Msg.Data to Channel.
   --
   -- Implementation Notes:
   --    Check status of Socket before sending data. If the Socket has data
   --    waiting to be read, Success is set to false, and the channel is read
   --    until an exception is raised (to clear the channel).
   --
   --------------------------------------------------------------------
   procedure SendMsg (Server  : in     ServerT;
                      Msg     : in     MessageT;
                      Success :    out Boolean)
   is
   begin
      Success := False;

      GNAT.Sockets.Set ( Item   => WriteSet,
                         Socket => PortTo(Server).Socket );

      GNAT.Sockets.Check_Selector ( Selector     => Selector,
                                    R_Socket_Set => ReadSet,
                                    W_Socket_Set => WriteSet,
                                    Status       => CheckStatus,
                                    Timeout      => 0.01 );

      if GNAT.Sockets.Is_Set ( Item   => ReadSet,
                               Socket => PortTo(Server).Socket ) then

         GNAT.Sockets.Clear ( Item   => ReadSet,
                              Socket => PortTo(Server).Socket );

         declare
            DummyChar : Character;
         begin
            for i in MessageIndexT'Range loop
               Character'Read ( PortTo(Server).Channel,
                                DummyChar );
            end loop;

         exception
            when E : others =>
               DebugOutput("Socket had readable data.");

         end;

      elsif GNAT.Sockets.Is_Set ( Item   => WriteSet,
                                  Socket => PortTo(Server).Socket ) then

         GNAT.Sockets.Clear ( Item   => WriteSet,
                              Socket => PortTo(Server).Socket );

         Success := True;

         for i in MessageIndexT range 1 .. Msg.Length loop

            Character'Write ( PortTo(Server).Channel,
                              Msg.Data(i) );

         end loop;

         Character'Write ( PortTo(Server).Channel,
                           ASCII.Cr );
         Character'Write ( PortTo(Server).Channel,
                           ASCII.Lf );

      end if;

      -- For debugging...
      DebugOutput("Sent: " & Msg.Data(1..Msg.Length));

   exception
      when E : others =>
         DebugOutput("Send Error.");
   end SendMsg;

   ------------------------------------------------------------------
   -- CommsIsOK
   --
   -- Description:
   --    Extracts the value corresponding to the SPRE response code from Msg.
   --    Returns true if the code is 'OK'.
   --
   -- Implementation notes:
   --    Find the first quote, and check the value of the next two characters.
   --
   ------------------------------------------------------------------
   function CommsIsOK (Msg : MessageT) return Boolean is
      CodeStart : MessageLengthT;
   begin
      CodeStart := Ada.Strings.Fixed.Index(Source  => Msg.Data(1..Msg.Length),
                                           Pattern => "'") + 1;
      return Msg.Data(CodeStart..CodeStart+1) = "OK";
   end CommsIsOk;

   --------------------------------------------------------------------
   --
   -- Exported Subprograms
   --
   --------------------------------------------------------------------
   --------------------------------------------------------------------
   -- ConnectToSPRE
   --
   -- Implementation Notes:
   --    Initializes the socket library.
   --
   --------------------------------------------------------------------
   procedure ConnectToSPRE (IsAdmin : in     Boolean;
                            Success :    out Boolean)
   is
      Address      : GNAT.Sockets.Sock_Addr_Type := GNAT.Sockets.No_Sock_Addr;
      Server       : ServerT;
      DummyMessage : MessageT;
      ReadOK       : Boolean := False;
   begin
      -- First ensure that socket library is available.
      if WinSockState = Uninitialized then

         pragma Warnings (Off);
         --  The following call is no longer needed with latst GNAT version
         GNAT.Sockets.Initialize;
         pragma Warnings (On);
         WinSockState := Initialized;

         GNAT.Sockets.Create_Selector ( Selector => Selector );
      end if;


      -- Set up socket address and Server into PortTo
      Address.Addr := GNAT.Sockets.Addresses
        (E => GNAT.Sockets.Get_Host_By_Name
              (Name => SPREMachine.Data(1 .. SPREMachine.Length) ),
         N => 1);

      if IsAdmin then
         Address.Port := AdminPort;
         Server       := Admin;
      else
         Address.Port := PortalPort;
         Server       := Portal;
      end if;


      -- If we are already connected, then do nothing.
      if PortTo(Server).State = NotConnected then

         GNAT.Sockets.Create_Socket ( Socket => PortTo(Server).Socket );

         GNAT.Sockets.Set_Socket_Option (
             Socket => PortTo(Server).Socket,
             Level  => GNAT.Sockets.Socket_Level,
             Option => ( Name    => GNAT.Sockets.Reuse_Address,
                         Enabled => True ));

         GNAT.Sockets.Connect_Socket ( Socket => PortTo(Server).Socket,
                                       Server => Address );
         PortTo(Server).Channel := GNAT.Sockets.Stream (PortTo(Server).Socket);

         PortTo(Server).State := Connected;

         -- A message should be sent back, don't care about the
         -- content, just read and discard.
         if MsgToRead( Server => Server ) then

            ReadMsg ( Server  => Server,
                      Msg     => DummyMessage,
                      Success => ReadOK );

         end if;

      end if;

      -- Return success unless exception.
      Success := ReadOK;

   exception
      when E : others =>

         if IsAdmin then
            DebugOutput(   "Error connecting to server... "
                           & SPREMachine.Data(1 .. SPREMachine.Length)
                           & " Port"
                           & GNAT.Sockets.Port_Type'Image(AdminPort));
         else
            DebugOutput(   "Error connecting to server... "
                           & SPREMachine.Data(1 .. SPREMachine.Length)
                           & " Port"
                           & GNAT.Sockets.Port_Type'Image(PortalPort));
         end if;

         if PortTo(Server).State = Connected then
            GNAT.Sockets.Close_Socket (PortTo(Server).Socket);
         end if;
         Success := False;
   end ConnectToSPRE;

   --------------------------------------------------------------------
   -- DisconnectFromSPRE
   --
   -- Implementation Notes:
   --    Finalizes the socket library if both ports are disconnected.
   --
   --------------------------------------------------------------------
   procedure DisconnectFromSPRE (IsAdmin : in     Boolean;
                                 Success :    out Boolean)
   is
      Address      : GNAT.Sockets.Sock_Addr_Type := GNAT.Sockets.No_Sock_Addr;
      Server       : ServerT;
      OtherDevice  : ServerT;
      SendOK       : Boolean  := False;
   begin

      if WinSockState = Initialized then
         -- Set up socket address and Server into PortTo
         Address.Addr := GNAT.Sockets.Addresses
           (GNAT.Sockets.Get_Host_By_Name
                (SPREMachine.Data(1 .. SPREMachine.Length)),
            1);

         if IsAdmin then
            Address.Port := AdminPort;
            Server       := Admin;
            OtherDevice  := Portal;
         else
            Address.Port := PortalPort;
            Server       := Portal;
            OtherDevice  := Admin;
         end if;

         -- If we are not connected, then do nothing.
         if PortTo(Server).State = Connected then

            GNAT.Sockets.Close_Socket ( PortTo(Server).Socket );

            PortTo(Server).Socket  := GNAT.Sockets.No_Socket;
            PortTo(Server).Channel :=
              GNAT.Sockets.Stream (GNAT.Sockets.No_Socket);
            PortTo(Server).State   := NotConnected;

         end if;

         -- If all ports are closed, finalize socket library
         if PortTo(OtherDevice).State = NotConnected then

            GNAT.Sockets.Close_Selector ( Selector => Selector );
            pragma Warnings (Off);
            --  The following call is no longer needed with latest GNAT version
            GNAT.Sockets.Finalize;
            pragma Warnings (On);
            WinSockState := Uninitialized;

         end if;

      end if;

      Success := True;

   exception
      when E : others =>

         if IsAdmin then
            DebugOutput(   "Error disconnecting from server... "
                           & SPREMachine.Data(1 .. SPREMachine.Length)
                           & " Port"
                           & GNAT.Sockets.Port_Type'Image(AdminPort));
         else
            DebugOutput(   "Error disconnecting from server... "
                           & SPREMachine.Data(1 .. SPREMachine.Length)
                           & " Port"
                           & GNAT.Sockets.Port_Type'Image(PortalPort));
         end if;

         if PortTo(Server).State = Connected then
            GNAT.Sockets.Close_Socket (PortTo(Server).Socket);
         end if;
         Success := False;
   end DisconnectFromSPRE;

   --------------------------------------------------------------------
   -- OpenAll
   --
   -- Implementation Notes:
   --    Suppress success flags - TIS will shutdown after failure to
   --    communicate with peripherals.
   --
   --------------------------------------------------------------------
   procedure OpenAll (Success : out Boolean)
   is
      ConnectOK : Boolean;
   begin
      StartDebug;

      ConnectToSPRE (IsAdmin => True,
                     Success => Success);
      ConnectToSPRE (IsAdmin => False,
                     Success => ConnectOK);
      Success := Success and ConnectOK;

   end OpenAll;

   --------------------------------------------------------------------
   -- CloseAll
   --
   -- Implementation Notes:
   --    Suppress success flags - TIS will force closure by shutting down.
   --
   --------------------------------------------------------------------
   procedure CloseAll
   is
      Ignored : Boolean;
   begin
      DisconnectFromSPRE (IsAdmin => False,
                          Success => Ignored);
      DisconnectFromSPRE (IsAdmin => True,
                          Success => Ignored);

   end CloseAll;

   --------------------------------------------------------------------
   -- SendAndReceive
   --
   -- Implementation Notes:
   --    None.
   --
   --------------------------------------------------------------------
   procedure SendAndReceive (IsAdmin  : in     Boolean;
                             Outgoing : in     MessageT;
                             Incoming :    out MessageT;
                             Success  :    out Boolean)
   is
      Address : GNAT.Sockets.Sock_Addr_Type := GNAT.Sockets.No_Sock_Addr;
      Server  : ServerT;
      SendOK  : Boolean := False;
      ReadOK  : Boolean := False;
   begin

      if WinSockState = Initialized then

         -- Set up socket address and Server details
         Address.Addr := GNAT.Sockets.Addresses
            (GNAT.Sockets.Get_Host_By_Name
                 (SPREMachine.Data(1 .. SPREMachine.Length)),
             1);

         if IsAdmin then
            Address.Port := AdminPort;
            Server       := Admin;
         else
            Address.Port := PortalPort;
            Server       := Portal;
         end if;

         -- Communicate with the server
         if PortTo(Server).State = Connected then

            SendMsg  ( Server  => Server,
                       Msg     => Outgoing,
                       Success => SendOK );

            if MsgToRead( Server => Server ) then

               ReadMsg ( Server  => Server,
                         Msg     => Incoming,
                         Success => ReadOK );

            end if;

         end if;

      end if;

      Success := SendOK and ReadOK and CommsIsOK(Msg => InComing);

   exception
      when E : others =>

         DebugOutput( "Error communicating with server. " );
         Success := False;
   end SendAndReceive;

   --------------------------------------------------------------------
   -- Init
   --
   -- Implementation Notes:
   --    None.
   --
   --------------------------------------------------------------------
   procedure Init (Success :    out Boolean)
   is
      Arg_Count : constant Natural := Ada.Command_Line.Argument_Count;

      InvalidArgument : exception;

      procedure PrintHelp is
      begin
         Ada.Text_IO.Put_Line("Optional arguments are:");
         Ada.Text_IO.Put_Line("[<device server name> [<Workstation port> [<Portal #1 port>]]]");
         Ada.Text_IO.Put_Line("where <device server name> must not exceed 30 characters");
         Ada.Text_IO.Put_Line("                           - default value: " &
                              SPREMachine.Data(1..SPREMachine.Length));
         Ada.Text_IO.Put_Line("      <Workstation port>   is a numeric");
         Ada.Text_IO.Put_Line("                           - default value: " &
                              GNAT.Sockets.Port_Type'Image(AdminPort));
         Ada.Text_IO.Put_Line("      <Portal #1 port>     is a numeric ");
         Ada.Text_IO.Put_Line("                           - default value: " &
                              GNAT.Sockets.Port_Type'Image(PortalPort));

      end PrintHelp;

   begin
      pragma Warnings (Off);
      --  The following call is no longer needed with latest GNAT version
      GNAT.Sockets.Initialize; -- needed so we can safely call Host_Name below.
      pragma Warnings (On);

      Success := True;
      case Arg_Count is
         when 0 =>
            -- No argument, so default to localhost
            declare
               This_Host : constant String := GNAT.Sockets.Host_Name;
            begin
               if This_Host'Last > SPREMachine.Data'Last then
                  raise InvalidArgument;
               else
                  SPREMachine.Data
                    (1 .. This_Host'Last) := This_Host;
                  SPREMachine.Length := This_Host'Last;
               end if;
            end;
         when 1 | 2 | 3 =>
            if Ada.Command_Line.Argument(1) = "help" then
               PrintHelp;
               Success := False;
            else
               if Ada.Command_Line.Argument(1)'Last > SPREMachine.Data'Last then
                  raise InvalidArgument;
               else
                  SPREMachine.Data (1 .. Ada.Command_Line.Argument(1)'Last) :=
                    Ada.Command_Line.Argument(1);
                  SPREMachine.Length := Ada.Command_Line.Argument(1)'Last;
               end if;
               if Arg_Count >= 2 then
                  AdminPort :=
                    GNAT.Sockets.Port_Type'Value(Ada.Command_Line.Argument(2));
               end if;
               if Arg_Count >= 3 then
                  PortalPort :=
                    GNAT.Sockets.Port_Type'Value(Ada.Command_Line.Argument(3));
               end if;
            end if;
         when others =>
            Ada.Text_IO.Put_Line("Wrong number of Arguments - optional arguments are:");
            Ada.Text_IO.Put_Line("  [<device server name> [<Workstation port> [<Portal #1 port>]]]");
            Ada.Text_IO.Put_Line("  supply single argument 'help' for more information");
            Success := False;
      end case;

   exception

      when E : others =>

         Success := False;
         Ada.Text_IO.Put_Line("Invalid Arguments - optional arguments are:");
         Ada.Text_IO.Put_Line("  [<device server name> [<Workstation port> [<Portal #1 port>]]]");
         Ada.Text_IO.Put_Line("  supply single argument 'help' for more information");

   end Init;

end TcpIp;
