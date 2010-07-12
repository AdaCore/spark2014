------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  IPdump
--  Test IP header decoding functions

with Ada.Streams; use Ada.Streams;
with Ada.Text_IO; use Ada.Text_IO;
with System;

with AIP.Checksum;
with AIP.Conversions;
with AIP.IPH; use AIP.IPH;

procedure IPdump is
   use type AIP.M16_T;

   Packet : Stream_Element_Array (1 .. 20) :=
     (16#45#, --  Version 4 / Length 5*4
      0,      --  Diffserv
      0,      --  Lenth: 145
      16#91#,
      16#38#, --  Ident 0x3898
      16#98#,
      16#40#, --  Flags 0x4, Fragoff 0,
      0,
      16#40#, --  TTL 64
      6,      --  Proto TCP
      3,      --  Cksum 0x03cd
      16#cd#,
      16#7f#, -- Src 127.0.0.1
      0,
      0,
      1,
      16#7f#, -- Dst 127.0.0.1
      0,
      0,
      1);
   for Packet'Alignment use 4;

   Ihdr : AIP.IPH.IP_Header;
   for Ihdr'Address use Packet'Address;

   procedure Show (F : String; V : Integer) is
      package AIO is new Ada.Text_IO.Integer_IO (Integer);
   begin
      Put (F & ASCII.HT);
      if F'Length < 8 then
         Put (ASCII.HT);
      end if;
      Put (V'Img);
      Put (ASCII.HT);
      AIO.Put (V, Base => 16);
      New_Line;
   end Show;

   Ihdr_Ptr : constant AIP.IPTR_T := AIP.Conversions.To_IPTR (Ihdr'Address);

begin
   Show ("Version", Integer (AIP.IPH.IPH_Version (Ihdr)));
   Show ("IHL", Integer (AIP.IPH.IPH_IHL (Ihdr)));
   Show ("TOS", Integer (AIP.IPH.IPH_TOS (Ihdr)));
   Show ("Length", Integer (AIP.IPH.IPH_Length (Ihdr)));
   Show ("Ident", Integer (AIP.IPH.IPH_Ident (Ihdr)));
   Show ("Flags", Integer (AIP.IPH.IPH_Flags (Ihdr)));
   Show ("Frag_Offset", Integer (AIP.IPH.IPH_Frag_Offset (Ihdr)));
   Show ("TTL", Integer (AIP.IPH.IPH_TTL (Ihdr)));
   Show ("Protocol", Integer (AIP.IPH.IPH_Protocol (Ihdr)));
   Show ("Checksum", Integer (AIP.IPH.IPH_Checksum (Ihdr)));
   Show ("Src_Address", Integer (AIP.IPH.IPH_Src_Address (Ihdr)));
   Show ("Dst_Address", Integer (AIP.IPH.IPH_Dst_Address (Ihdr)));
   --  Show ("Options", Integer (AIP.IPH.IPH_Options (Ihdr)));
   --  Show ("Padding", Integer (AIP.IPH.IPH_Padding (Ihdr)));

   New_Line;
   Show ("ComputedCksum",
     Integer (AIP.Checksum.Checksum
                (Ihdr_Ptr, 4 * Natural (AIP.IPH.IPH_IHL (Ihdr)))));

   New_Line;
   AIP.IPH.Set_IPH_Checksum (Ihdr, 0);
   Show ("ReComputedCksum",
     Integer (not AIP.Checksum.Checksum
                (Ihdr_Ptr, 4 * Natural (AIP.IPH.IPH_IHL (Ihdr)))));

end IPdump;
