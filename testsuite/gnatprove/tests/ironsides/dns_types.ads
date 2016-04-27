----------------------------------------------------------------
-- IRONSIDES - DNS SERVER
--
-- By: Martin C. Carlisle and Barry S. Fagin
--     Department of Computer Science
--     United States Air Force Academy
--
-- Modified by: Altran UK Limited
--
-- This is free software; you can redistribute it and/or
-- modify without restriction.  We do ask that you please keep
-- the original author information, and clearly indicate if the
-- software has been modified.
--
-- This software is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty
-- of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
----------------------------------------------------------------

with System;

package DNS_Types is
   Packet_Size : constant := 8192;
   Header_Bits : constant := 96;

   type QName_Ptr_Range is range 0 .. 2**14-1;

   type Packet_Length_Range is range 0 .. Packet_Size;

   UDP_Max_Size : constant Packet_Length_Range := 512;

   type Packet_Bytes_Range is range 1 .. Packet_Size - Header_Bits/8;

   type Byte is mod 256;
   for Byte'Size use 8;

   type Unsigned_Short is range 0 .. 2**16 - 1;
   for Unsigned_Short'Size use 16;

   -- used in OPCode field below
   type Opcode_Type is (Query, IQuery, Status);
   for Opcode_Type'Size use 4;

   -- used in RCode field below
   type Response_Code is (No_Error,
                          Format_Error,
                          Server_Failure,
                          Name_Error,
                          Not_Implemented,
                          Refused);
   for Response_Code'Size use 4;


   -- See http://www.zytrax.com/books/dns/ch15/ for a description
   -- of these fields.
   type Header_Type is record
      -- 16 bit message ID supplied by requester and mirrored by responder
      MessageID : Unsigned_Short;
      -- False for query, true for response
      QR        : Boolean;
      -- 0 for query, 1 for inverse query, 2 for status request
      Opcode    : Opcode_Type;
      -- Authoritative Answer (response only)
      AA        : Boolean;
      -- Truncated (partial message, true until last portion)
      TC        : Boolean;
      -- recursion desired (query)
      RD        : Boolean;
      -- recursion available (response)
      RA        : Boolean;
      -- Reserved for future use (zone transfers??)
      Res1      : Boolean;
      Res2      : Boolean;
      Res3      : Boolean;
      -- response code.
      RCode     : Response_Code;
      -- number of queries (echo in answer!)
      QDCount   : Unsigned_Short;
      -- number of answers
      ANCount   : Unsigned_Short;
      -- number of name server resource records
      NSCount   : Unsigned_Short;
      -- number of additional records
      ARCount   : Unsigned_Short;
   end record;

   --   for Header use record
   --      MessageID at 0 range 0..15;
   --      QR at 0 range 23..23;
   --      Opcode at 0 range 19..22;
   --      AA at 0 range 18..18;
   --      TC at 0 range 17..17;
   --      RD at 0 range 16..16;
   --      RA at 0 range 31..31;
   --      Res1 at 0 range 30..30;
   --      Res2 at 0 range 29..29;
   --      Res3 at 0 range 28..28;
   --      RCode at 0 range 24..27;
   --      QDCount at 4 range 0..15;
   --      ANCount at 4 range 16..31;
   --      NSCount at 8 range 0..15;
   --      ARCount at 8 range 16..31;
   --   end record;
   --   for Header'Bit_Order use System.Low_Order_First;

   for Header_Type use record
      MessageID at 0 range 16 .. 31;
      QR        at 0 range 8 .. 8;
      Opcode    at 0 range 9 .. 12;
      AA        at 0 range 13 .. 13;
      TC        at 0 range 14 .. 14;
      RD        at 0 range 15 .. 15;
      RA        at 0 range 0 .. 0;
      Res1      at 0 range 1 .. 1;
      Res2      at 0 range 2 .. 2;
      Res3      at 0 range 3 .. 3;
      RCode     at 0 range 4 .. 7;
      QDCount   at 4 range 16 .. 31;
      ANCount   at 4 range 0 .. 15;
      NSCount   at 8 range 16 .. 31;
      ARCount   at 8 range 0 .. 15;
   end record;
   for Header_Type'Size use Header_Bits;
   for Header_Type'Bit_Order use System.High_Order_First;

   Empty_Header : constant Header_Type :=
     Header_Type'(MessageID => 0,
                  QR        => False,
                  Opcode    => Query,
                  Rcode     => No_Error,
                  AA        => False,
                  TC        => False,
                  RD        => False,
                  RA        => False,
                  Res1      => False,
                  Res2      => False,
                  Res3      => False,
                  QDCount   => 0,
                  ANCount   => 0,
                  NSCount   => 0,
                  ARCount   => 0);

   function Byte_Swap_US (U : Unsigned_Short) return Unsigned_Short;
   pragma Inline(Byte_Swap_US);

   -- swap bytes in Unsigned_Short fields
   -- to switch between network and host order for little endian machines
   procedure Byte_Swap (H : in out Header_Type)
   with Depends => (H =>+ null),
        Post    =>
     H = H'Old'Update (MessageID => Byte_Swap_US (H'Old.MessageID),
                       QDCount   => Byte_Swap_US (H'Old.QDCount),
                       ANCount   => Byte_Swap_US (H'Old.ANCount),
                       NSCount   => Byte_Swap_US (H'Old.NSCount),
                       ARCount   => Byte_Swap_US (H'Old.ARCount));

   type Query_Class is (IN_Class,
                        CH_Class,
                        HS_Class,
                        None_Class,
                        Any_Class);
   for Query_Class use (IN_Class   => 1,
                        CH_Class   => 3,
                        HS_Class   => 4,
                        None_Class => 254,
                        Any_Class  => 255);
   for Query_Class'Size use 16;

   type Query_Type is (A,
                       NS,
                       CName,
                       SOA,
                       WKS,
                       Ptr,
                       MX,
                       AAAA,
                       Srv,
                       A6,
                       OPT,
                       --DNSSEC
                       DS,
                       RRSig,
                       NSec,
                       DNSKey,
                       --
                       Any,
                       CAA,
                       Error,
                       Unimplemented);
   for Query_Type use (A             => 1,
                       NS            => 2,
                       CName         => 5,
                       SOA           => 6,
                       WKS           => 11,
                       Ptr           => 12,
                       MX            => 15,
                       AAAA          => 28,
                       Srv           => 33,
                       A6            => 38,
                       OPT           => 41,
                       DS            => 43,
                       RRSig         => 46,
                       NSec          => 47,
                       DNSKey        => 48,
                       Any           => 255,
                       CAA           => 257,
                       Error         => 65280,
                       Unimplemented => 65281);
   for Query_Type'Size use 16;

   type EDNS_Record is record
      Root         : Character;
      Code         : Query_Type;
      Payload_Size : Unsigned_Short;
      RCode        : Byte;
      Version      : Byte;
      ZTop         : Byte;
      ZBottom      : Byte;
      RDLen        : Unsigned_Short;
   end record;
   --this record won't pack b/c payload_size isn't aligned correctly.
   --for EDNS_Record'Size use 9*8;
   --for EDNS_Record'Bit_Order use System.High_Order_First;
   DNSSecMask : constant := 128;

   type Bytes_Array_Type is array (Packet_Bytes_Range) of Byte;

   type DNS_Packet is record
      Header : Header_Type;
      Bytes  : Bytes_Array_Type;
   end record;
   type DNS_TCP_Packet is record
      Length : Unsigned_Short;
      Rest   : DNS_Packet;
   end record;
end DNS_Types;
