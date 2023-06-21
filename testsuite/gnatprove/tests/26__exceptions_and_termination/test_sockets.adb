with Ada.Strings.Unbounded;

procedure Test_Sockets with SPARK_Mode is

   package Sockets is
      type Socket_Type is private;
      --  Sockets are used to implement a reliable bi-directional point-to-point,
      --  stream-based connections between hosts. No_Socket provides a special
      --  value to denote uninitialized sockets.

      No_Socket : constant Socket_Type;

      Socket_Error : exception;
      --  There is only one exception in this package to deal with an error during
      --  a socket routine. Once raised, its message contains a string describing
      --  the error code.

      type Family_Type is (Family_Inet, Family_Inet6, Family_Unix, Family_Unspec);
      --  Address family (or protocol family) identifies the communication domain
      --  and groups protocols with similar address formats.
      --  The order of the enumeration elements should not be changed unilaterally
      --  because the IPv6_TCP_Preferred routine rely on it.

      subtype Family_Inet_4_6 is Family_Type range Family_Inet .. Family_Inet6;

      type Mode_Type is (Socket_Stream, Socket_Datagram, Socket_Raw);
      --  Stream sockets provide connection-oriented byte streams. Datagram
      --  sockets support unreliable connectionless message-based communication.
      --  Raw sockets provide raw network-protocol access.
      --  The order of the enumeration elements should not be changed unilaterally
      --  because the IPv6_TCP_Preferred routine relies on it.

      type Shutmode_Type is (Shut_Read, Shut_Write, Shut_Read_Write);
      --  When a process closes a socket, the policy is to retain any data queued
      --  until either a delivery or a timeout expiration (in this case, the data
      --  are discarded). Finer control is available through shutdown. With
      --  Shut_Read, no more data can be received from the socket. With_Write, no
      --  more data can be transmitted. Neither transmission nor reception can be
      --  performed with Shut_Read_Write.

      type Port_Type is range 0 .. 16#ffff#;
      --  TCP/UDP port number

      type Inet_Addr_Comp_Type is mod 2 ** 8;
      --  Octet for Internet address

      Inet_Addr_Bytes_Length : constant array (Family_Inet_4_6) of Natural :=
        [Family_Inet => 4, Family_Inet6 => 16];

      type Inet_Addr_Bytes is array (Natural range <>) of Inet_Addr_Comp_Type;

      subtype Inet_Addr_V4_Type is
        Inet_Addr_Bytes (1 ..  Inet_Addr_Bytes_Length (Family_Inet));
      subtype Inet_Addr_V6_Type is
        Inet_Addr_Bytes (1 ..  Inet_Addr_Bytes_Length (Family_Inet6));

      subtype Inet_Addr_VN_Type is Inet_Addr_Bytes;
      --  For backwards compatibility

      type Inet_Addr_Type (Family : Family_Inet_4_6 := Family_Inet) is record
         case Family is
         when Family_Inet =>
            Sin_V4 : Inet_Addr_V4_Type := [others => 0];

         when Family_Inet6 =>
            Sin_V6 : Inet_Addr_V6_Type := [others => 0];

         end case;
      end record;

      type Sock_Addr_Type (Family : Family_Type := Family_Inet) is record
         case Family is
         when Family_Unix =>
            Name : Ada.Strings.Unbounded.Unbounded_String;
         when Family_Inet_4_6 =>
            Addr : Inet_Addr_Type (Family);
            Port : Port_Type;
         when Family_Unspec =>
            null;
         end case;
      end record;

      function Is_Connected (Socket : Socket_Type) return Boolean with
        Import,
        Ghost,
        Global => null;

      procedure Connect_Socket
        (Socket : aliased in out Socket_Type;
         Server : in out Sock_Addr_Type)
      with Import,
        Global => null,
        Always_Terminates,
        Pre  => not Is_Connected (Socket),
        Post => Is_Connected (Socket),
        Exceptional_Cases => (Socket_Error => not Is_Connected (Socket));
      --  Make a connection to another socket which has the address of
      --  Server. Raise Socket_Error on error.
   private
      pragma SPARK_Mode (Off);
      type Socket_Type is new Integer;
      No_Socket : constant Socket_Type := -1;
   end Sockets;
   use Sockets;

   procedure Retry_Connect_Socket
     (Socket  : aliased in out Socket_Type;
      Server  : in out Sock_Addr_Type;
      Try_Num : Natural)
   with
     Always_Terminates => Try_Num /= 0,
     Pre  => not Is_Connected (Socket),
     Post => Is_Connected (Socket),
     Exceptional_Cases =>
         (Socket_Error => Try_Num /= 0 and then not Is_Connected (Socket));

   procedure Retry_Connect_Socket
     (Socket  : aliased in out Socket_Type;
      Server  : in out Sock_Addr_Type;
      Try_Num : Natural)
   is
   begin
      if Try_Num = 0 then
         loop
            pragma Loop_Invariant (not Is_Connected (Socket));
            begin
               Connect_Socket (Socket, Server);
               return;
            exception
               when Socket_Error =>
                  null;
            end;
         end loop;
      else
         for K in 1 .. Try_Num - 1 loop
            pragma Loop_Invariant (not Is_Connected (Socket));
            begin
               Connect_Socket (Socket, Server);
               return;
            exception
               when Socket_Error =>
                  null;
            end;
         end loop;
         Connect_Socket (Socket, Server);
      end if;
   end Retry_Connect_Socket;

begin
   null;
end Test_Sockets;
