------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                       M E M C A C H E _ C L I E N T                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2017-2020, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Latin_1;
with Ada.Streams;
with Ada.Strings.Fixed;     use Ada.Strings.Fixed;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

package body Memcache_Client is

   --  Implementing some parts of the memcached protocol

   --  https://github.com/memcached/memcached/blob/master/doc/protocol.txt

   CRLF : constant String :=
     Ada.Characters.Latin_1.CR &
     Ada.Characters.Latin_1.LF;

   function Read_Stop_When_End_Marker
     (Conn       : Cache_Connection;
      End_Marker : String)
      return String;
   --  @param Conn the connection from which to read
   --  @param End_Marker when the read text ends with this marker, stop
   --    reading. Reading will *not* stop if the end marker appears somewhere
   --    inside a message. But this shouldn't happen in regular connections.
   --  @return the read text

   ----------
   -- Init --
   ----------

   function Init
     (Hostname : String;
      Port     : Port_Type) return Cache_Connection
   is
      Host : constant Host_Entry_Type := Get_Host_By_Name (Hostname);
      Result : Cache_Connection;
      Status : Boolean;
   begin
      Create_Socket (Result.Sock);

      --  Make socket available only to wrapper, not to the wrapped executable
      Set_Close_On_Exec (Socket        => Result.Sock,
                         Close_On_Exec => True,
                         Status        => Status);

      pragma Assert (Status);

      Connect_Socket (Result.Sock,
                      (Family => Family_Inet,
                       Addr   => Addresses (Host),
                       Port   => Port));
      Result.Stream := Stream (Result.Sock);
      return Result;
   end Init;

   -------------------------------
   -- Read_Stop_When_End_Marker --
   -------------------------------

   function Read_Stop_When_End_Marker
     (Conn : Cache_Connection;
      End_Marker : String)
      return String
   is
      Buf : Ada.Streams.Stream_Element_Array (1 .. 1024);
      Result : Unbounded_String := Null_Unbounded_String;
      Last : Ada.Streams.Stream_Element_Offset;
   begin
      loop
         Receive_Socket (Conn.Sock, Buf, Last);
         declare
            Read_Str : String (Integer (Buf'First) .. Integer (Last));
         begin
            for I in Buf'First .. Last loop
               Read_Str (Integer (I)) := Character'Val (Buf (I));
            end loop;
            Append (Result, Read_Str);
            exit when Tail (Result, End_Marker'Length) = End_Marker;
         end;
      end loop;
      return To_String (Result);
   end Read_Stop_When_End_Marker;

   ---------
   -- Set --
   ---------

   procedure Set
     (Conn  : Cache_Connection;
      Key   : String;
      Value : String)
   is
      Len : constant Natural := Value'Length;
   begin

      --  Hardcoding unused flag and expiration values

      String'Write (Conn.Stream, "set " & Key & " 0 0" &
                      Natural'Image (Len) & CRLF);

      --  The stored value might be arbitrarily large, so we need to send it
      --  separately, i.e. without concatenating with the "set ..." command
      --  using "&" operator, because that would create a temporary object that
      --  might cause stack to overflow.

      String'Write (Conn.Stream, Value);
      String'Write (Conn.Stream, CRLF);

      declare
         Answer : constant String := Read_Stop_When_End_Marker (Conn, CRLF);

      begin
         --  We expect the key-value pair to be stored

         if Answer = "STORED" & CRLF then
            null;

         --  Silenlty ignore server-side errors, e.g. when the value object is
         --  too large. ??? ideally such errors should be propagated to users

         elsif Head (Answer, 13) = "SERVER_ERROR "
           and then Tail (Answer, 2) = CRLF
         then
            null;

         else
            raise Program_Error;
         end if;
      end;
   end Set;

   ---------
   -- Get --
   ---------

   function Get (Conn : Cache_Connection; Key : String) return String is
   begin
      String'Write (Conn.Stream, "get " & Key & CRLF);
      declare
         Answer : constant String :=
           Read_Stop_When_End_Marker (Conn, "END" & CRLF);
         Start  : constant Integer := Ada.Strings.Fixed.Index (Answer, CRLF);
      begin
         --  We remove the first line from the output, as well as the last
         --  line containing the END marker, and also the previous CRLF line
         --  separator. The result may be empty.

         return Answer (Start + 2 .. Answer'Last - 7);
      end;
   end Get;

   -----------
   -- Close --
   -----------

   procedure Close (Conn : in out Cache_Connection) is
   begin
      Free (Conn.Stream);
      Close_Socket (Conn.Sock);
   end Close;

end Memcache_Client;
