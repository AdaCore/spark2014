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

with System,
     Protected_SPARK_IO_05,
     DNS_Types,
     Unsigned_Types,
     DNS_Table_PKG,
     DNS_Network_Receive;

use type DNS_Types.Packet_Bytes_Range,
         DNS_Types.Packet_Length_Range,
         DNS_Types.Byte,
         DNS_Types.Query_Type,
         DNS_Types.Query_Class,
         Unsigned_Types.Unsigned8,
         Unsigned_Types.Unsigned16,
         Unsigned_Types.Unsigned32,
         DNS_Types.Unsigned_Short,
         DNS_Types.QName_Ptr_Range,
         System.Bit_Order;

--with Ada.Text_Io;
with Ada.Unchecked_Conversion;

package body Process_Dns_Request is
   procedure Set_Unsigned_32
     (Bytes      : in out DNS_Types.Bytes_Array_Type;
      Start_Byte : in     DNS_Types.Packet_Bytes_Range;
      Value      : in     Unsigned_Types.Unsigned32)
   is
   begin
      Bytes (Start_Byte)     := DNS_Types.Byte (Value/2**24);
      Bytes (Start_Byte + 1) := DNS_Types.Byte ((Value/2**16) mod 256);
      Bytes (Start_Byte + 2) := DNS_Types.Byte ((Value/2**8) mod 256);
      Bytes (Start_Byte + 3) := DNS_Types.Byte (Value mod 256);
   end Set_Unsigned_32;

   procedure Set_Unsigned_16
     (Bytes      : in out DNS_Types.Bytes_Array_Type;
      Start_Byte : in     DNS_Types.Packet_Bytes_Range;
      Value      : in     Unsigned_Types.Unsigned16)
   is
   begin
      Bytes (Start_Byte)     := DNS_Types.Byte ((Value/2**8) mod 256);
      Bytes (Start_Byte + 1) := DNS_Types.Byte (Value mod 256);
   end Set_Unsigned_16;

   procedure Set_TTL_Data_IP
     (Bytes      : in out DNS_Types.Bytes_Array_Type;
      Start_Byte : in     DNS_Types.Packet_Bytes_Range;
      A_Record   : in     RR_Type.A_Record_Type.ARecordType) is
   begin
      -- TTL
      Set_Unsigned_32(Bytes, Start_Byte, A_Record.TTLInSeconds);
      -- DATA 4 bytes
      Set_Unsigned_16(Bytes, Start_Byte+4, 4);
      -- IP address
      Set_Unsigned_32(Bytes, Start_Byte+6, A_Record.IPV4);
   end Set_TTL_Data_IP;

   --base64 conversion
   function Lookup (Arg: in Character) return DNS_Types.Byte is
      ANS : DNS_Types.Byte;
   begin
      case Arg is
         when 'A'..'Z' => ANS := Character'Pos( Arg) - Character'Pos ('A');
         when 'a'..'z' => ANS := (Character'Pos (Arg) - Character'Pos ('a'))+26;
         when '0'..'9' => ANS := (Character'Pos (Arg) - Character'Pos ('0'))+52;
         when '+' => ANS := 62;
         when '/' => ANS := 63;
         when others => ANS := 0;
      end case;
      return ans;
   end Lookup;

   --see http://rfc-ref.org/RFC-TEXTS/4034/chapter2.html for DNSKed record
   --format
   procedure Set_TTL_Data_DNSKey--BSF
     (Bytes         : in out DNS_Types.Bytes_Array_Type;
      Start_Byte    : in     DNS_Types.Packet_Bytes_Range;
      DNSKey_Record : in     RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      Dstbytes      :    out RR_Type.DNSKey_Record_Type.KeyLengthValueType)
   is
      SrcByte       : Integer;
      KeyLength     : RR_Type.DNSKey_Record_Type.KeyLengthValueType;
      SrcNum0, SrcNum1, SrcNum2, SrcNum3 : DNS_Types.Byte;
      DstNum0, DstNum1, DstNum2          : DNS_Types.Byte;
   begin
      -- TTL (4 bytes)
      Set_Unsigned_32 (Bytes,
                       Start_Byte,
                       DNSKey_Record.TTLInSeconds);
      --RDLength (2 bytes, value is 4 plus the length of the key, placeholder
      --at this point)
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       4 + Unsigned_Types.Unsigned16 (DNSKey_Record.KeyLength));
      -- RDATA (4 bytes)
      --   flags (2 bytes)
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 6,
                       DNSKey_Record.Flags);
      --   protocol (1 byte)
      Bytes (Start_Byte + 8) := DNS_types.Byte (DNSKey_Record.Protocol);
      --   algorithm (1 byte)
      Bytes (Start_Byte + 9) := DNS_types.Byte (DNSKey_Record.Algorithm);
      --   key field
      SrcByte := 1;
      DstBytes := 1;
      KeyLength := DNSKey_Record.KeyLength;
      while SrcByte + 3 <= KeyLength loop
         --since it's base64 encoded, src key will always contain an exact
         --multiple of 4 bytes
         pragma Loop_Invariant
           (SrcByte + 3 <= KeyLength and
            KeyLength <= RR_Type.DNSKey_Record_Type.MaxDNSKeyLength and
            KeyLength = DNSKey_Record.KeyLength and
            DstBytes >= 1 and
            DstBytes <= SrcByte and
            Start_Byte <= DNS_Types.Packet_Bytes_Range'Last - 10 -
                          DNS_Types.Packet_Bytes_Range
                            (DNSKey_Record.keyLength));
         srcNum0 := Lookup (DNSKey_Record.Key (SrcByte));       --00aaaaaa
         srcNum1 := Lookup (DNSKey_Record.Key (SrcByte + 1));   --00bbbbbb
         srcNum2 := Lookup (DNSKey_Record.Key (SrcByte + 2));   --00cccccc
         SrcNum3 := Lookup (DNSKey_Record.Key (SrcByte + 3));   --00dddddd

         DstNum0 := SrcNum0*4 + (Srcnum1/16);  --aaaaaa00 + 000000bb = aaaaaabb
         DstNum1 := Srcnum1*16 + (SrcNum2/4);  --bbbb0000 + 0000cccc = bbbbcccc
         DstNum2 := SrcNum2*64 + SrcNum3;      --cc000000 + 00dddddd = ccdddddd

         Bytes ((Start_Byte+9) + DNS_Types.Packet_Bytes_Range (DstBytes)) :=
           DstNum0;

         Bytes ((Start_Byte+9) + DNS_Types.Packet_Bytes_Range (DstBytes+1)) :=
           DstNum1;

         Bytes ((Start_Byte+9) + DNS_Types.Packet_Bytes_Range (DstBytes+2)) :=
           DstNum2;

         SrcByte := SrcByte + 4;
         DstBytes := DstBytes + 3;
      end loop;

      --RDLength (2 bytes, value is 4 plus the length of the key, which we now
      --know)
      DstBytes := Dstbytes - 1; --this is also an out parameter of this
                                --procedure
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       4 + Unsigned_Types.Unsigned16 (DstBytes));
   end Set_TTL_Data_DNSKey;

   --see http://tools.ietf.org/rfc/rfc3845.txt for NSEC wire format.  If you're
   --a masochist.
   procedure Set_TTL_Data_NSec--BSF
     (Bytes       : in out DNS_Types.Bytes_Array_Type;
      Start_Byte  : in     DNS_Types.Packet_Bytes_Range;
      NSec_Record : in     RR_Type.NSec_Record_Type.NSecRecordType;
      Dstbytes    :    out DNS_Types.Packet_Length_Range)
   is --bytes used in RRDada section
      Current_Name_Length : RR_Type.WireStringTypeIndex;
      BlockOffset : DNS_Types.Packet_Bytes_Range;
   begin
      -- TTL (4 bytes)
      Set_Unsigned_32 (Bytes,Start_Byte, NSec_Record.TTLInSeconds);
      -- RDLength (2 bytes, value will be the length of the domain name plus
      -- the length of the bitmapped RRList)
      -- placeholder for now
      Set_Unsigned_16 (Bytes, Start_Byte + 4, Unsigned_Types.Unsigned16 (0));

      -- NEXT DOMAIN NAME (Current_Name_Length bytes)
      Current_Name_Length :=
        RR_Type.WireNameLength (NSec_Record.NextDomainName);

      for I in RR_Type.WireStringTypeIndex range 1 .. Current_Name_Length loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 6) -
                          DNS_Types.Packet_Bytes_Range
                            (Current_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last and
            Current_Name_Length >= RR_Type.WireStringTypeIndex'First and
            Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
            (for all J in RR_Type.WireStringTypeIndex =>
               Character'Pos (NSec_Record.NextDomainName (J)) >= 0 and
               Character'Pos (NSec_Record.NextDomainName (J)) <= 255));

         Bytes (((Start_Byte + 6) - 1) + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (NSec_Record.NextDomainName (I)));
      end loop;

      -- RR bitmap section (ugh)
      DstBytes := 0;
      BlockOffset := ((Start_Byte + 6) - 1) +
                     DNS_Types.Packet_Bytes_Range (Current_Name_Length);

      for Block in RR_Type.NSec_Record_Type.BlockNumberValue
        range 1 .. NSec_Record.NumberOfBlocks
      loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 6) -
                          DNS_Types.Packet_Bytes_Range (Current_Name_Length) and
            Current_Name_Length >= RR_Type.WireStringTypeIndex'First and
            Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
            BlockOffset >= DNS_Types.Packet_Bytes_Range'First and
            BlockOffset <= (((Start_Byte + 6) - 1) +
                            DNS_Types.Packet_Bytes_Range
                              (Current_Name_Length)) +
                           DNS_Types.Packet_Bytes_Range
                             ((Block - 1) *
                              (2 + RR_Type.NSec_Record_Type.BlockLengthValue'Last)) and
            DstBytes <= DNS_Types.Packet_Length_Range
                          ((Block - 1) *
                           RR_Type.NSec_Record_Type.BlockLengthValue'Last) and
            NSec_Record.BlockLengths(Block) >=
              RR_Type.NSec_Record_Type.BlockLengthValue'First and
            NSec_Record.BlockLengths (Block) <=
              RR_Type.NSec_Record_Type.BlockLengthValue'Last);

         DstBytes := DstBytes + DNS_Types.Packet_Length_Range
                                  (NSec_Record.BlockLengths (Block));
         --sum up the block lengths, needed below

         Bytes (BlockOffset + 1) := NSec_Record.BlockNumbers (Block);
         Bytes (BlockOffset + 2) := DNS_Types.Byte
                                      (NSec_Record.BlockLengths (Block));

         for Byte in RR_Type.NSec_Record_Type.BlockLengthValue
           range 1 .. NSec_Record.BlockLengths (Block)
         loop

            pragma Loop_Invariant
              (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 6) -
                             DNS_Types.Packet_Bytes_Range
                               (Current_Name_Length) and
               Current_Name_Length >= RR_Type.WireStringTypeIndex'First and
               Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
               BlockOffset >= DNS_Types.Packet_Bytes_Range'First and
               BlockOffset <=
                 (((Start_Byte + 6) - 1) + DNS_Types.Packet_Bytes_Range
                                             (Current_Name_Length)) +
                 DNS_Types.Packet_Bytes_Range
                   ((Block - 1) *
                    (2 + RR_Type.NSec_Record_Type.BlockLengthValue'Last)) and
               DstBytes <= DNS_Types.Packet_Length_Range
                 (Block * RR_Type.NSec_record_type.BlockLengthValue'Last) and
               Byte >= RR_Type.NSec_Record_Type.BlockLengthValue'First and
               Byte <= rr_type.nsec_record_type.BlockLengthValue'Last and
               Block = Block'Loop_Entry);

            Bytes ((BlockOffset + 2) + DNS_Types.Packet_Bytes_Range (Byte)) :=
              NSec_Record.BitMaps (Block)(Byte);
         end loop;

         BlockOffset :=
           (BlockOffset + 2) +
           DNS_Types.Packet_Bytes_Range (NSec_Record.BlockLengths (Block));
      end loop;

      DstBytes :=
        DstBytes + DNS_Types.Packet_Length_Range (NSec_Record.NumberOfBlocks*2);
      --add in the bytes for the block numbers and the block lengths

      DstBytes :=
        DstBytes + DNS_Types.Packet_Length_Range (Current_Name_Length);
      --sets final value of OUT parameter

      --RDLength (2 bytes, can now set final value as the length of the domain
      --name plus the length of the bitmapped RRList)
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       Unsigned_Types.Unsigned16 (DstBytes));
   end Set_TTL_Data_NSec;

   --see http://www.rfc-editor.org/rfc/rfc4034.txt for RRSIG record format
   procedure Set_TTL_Data_RRSig--BSF
     (Bytes        : in out DNS_Types.Bytes_Array_Type;
      Start_Byte   : in     DNS_Types.Packet_Bytes_Range;
      RRSig_Record : in     RR_Type.RRSig_Record_Type.RRSigRecordType;
      DstBytes     :    out DNS_Types.Packet_Bytes_Range)
   is
      WireVersion         : RR_Type.WireStringType;
      Current_Name_Length : RR_Type.WireStringTypeIndex;
      SrcByte             : Integer;
      SigLength           : RR_Type.RRSig_Record_Type.SigLengthValueType;
      SigOffset           : DNS_Types.Packet_Bytes_Range;
      SrcNum0, SrcNum1, SrcNum2, SrcNum3: DNS_Types.Byte;
      DstNum0, DstNum1, DstNum2 : DNS_Types.Byte;

      function From_Query_Type is new Ada.Unchecked_Conversion
        (DNS_Types.Query_Type, Unsigned_Types.Unsigned32);

      function From_Bytes_Range is new Ada.Unchecked_Conversion
        (DNS_Types.Packet_Bytes_Range, Unsigned_Types.Unsigned32);
   begin
      -- TTL (4 bytes)
      Set_Unsigned_32 (Bytes, Start_Byte,RRSIG_Record.TTLInSeconds);
      -- RDLength (2 bytes, value is 18 plus the length of the name plus the
      -- length of the signature, placeholder at this point)
      Set_Unsigned_16 (Bytes, Start_Byte + 4, 0);
      -- TYPE COVERED (2 bytes)
      -- Ugh.  The things we do to make SPARK happy.  mod is superfluous, used
      --only to convince SPARK that the value is in type.
      Set_Unsigned_16
        (Bytes,
         Start_Byte + 6,
         Unsigned_Types.Unsigned16
           (From_Query_Type (RRSig_Record.TypeCovered) mod 65536));

      -- Algorithm (1 byte)
      Bytes (Start_Byte + 8) := DNS_Types.Byte (RRSig_Record.Algorithm);
      -- LABELS (1 byte)
      Bytes (Start_Byte + 9) := DNS_Types.Byte (RRSig_Record.NumLabels);
      -- ORIG TTL (4 bytes)
      Set_Unsigned_32 (Bytes, Start_Byte + 10, RRSig_Record.OrigTTL);
      -- SIG EXPIRATION (4 bytes)
      Set_Unsigned_32 (Bytes, Start_Byte + 14, RRSig_Record.SigExpiration);
      -- SIG INCEPTION (4 bytes) (starring Leonardo DiCaprio)
      Set_Unsigned_32 (Bytes, Start_Byte + 18, RRSig_Record.SigInception);
      -- KEY TAG (2 bytes)
      Set_Unsigned_16 (Bytes, Start_Byte + 22, RRSig_Record.KeyTag);

      -- SIGNER'S NAME (Current_Name_Length bytes)
      WireVersion := RR_Type.ConvertDomainNameToWire (RRSig_Record.SignerName);
      Current_Name_Length := RR_Type.WireNameLength (WireVersion);
      for I in RR_Type.WireStringTypeIndex range 1 .. Current_Name_Length loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 24) -
                          DNS_Types.Packet_Bytes_Range (Current_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last and
            Current_Name_Length >= RR_Type.WireStringTypeIndex'First and
            Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
            (for all J in RR_Type.WireStringTypeIndex =>
               Character'Pos (WireVersion (J)) >= 0 and
               Character'Pos (WireVersion(J)) <= 255));

         Bytes (((Start_Byte + 24) - 1) + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (WireVersion(I)));
      end loop;

      -- SIGNATURE
      SrcByte := 1;
      DstBytes := 1;
      SigLength := RRSig_Record.SignatureLength;
      SigOffset := (((Start_Byte + 24) - 1) +
                      DNS_Types.Packet_Bytes_Range (Current_Name_Length));
      --this+1 is the index of the first byte of the signature

      while (SrcByte + 3 <= SigLength) loop
         --since it's base64 encoded, src key will always contain an exact
         --multiple of 4 bytes

         pragma Loop_Invariant
           (SrcByte + 3 <= SigLength and
            SigLength <= RR_Type.RRSig_Record_Type.MaxRRSigLength and
            SigLength = RRSig_Record.SignatureLength and
            DstBytes >= DNS_Types.Packet_Bytes_Range (1) and
            DstBytes <= DNS_Types.Packet_Bytes_Range (SrcByte) and
            Start_Byte <= DNS_Types.Packet_Bytes_Range'Last - 24 -
                          DNS_Types.Packet_Bytes_Range
                            (RR_Type.MaxDomainNameLength) -
                          DNS_Types.Packet_Bytes_Range (SigLength) and
            Current_Name_Length >= RR_Type.WireStringTypeIndex'First and
            Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
            SigOffset = Start_Byte + 24 - 1 + DNS_Types.Packet_Bytes_Range
                                                (Current_Name_Length));

         SrcNum0 := Lookup (RRSig_Record.Signature (SrcByte));       --00aaaaaa
         SrcNum1 := Lookup (RRSig_Record.Signature (SrcByte + 1));   --00bbbbbb
         SrcNum2 := Lookup (RRSig_Record.Signature (SrcByte + 2));   --00cccccc
         SrcNum3 := Lookup (RRSig_Record.Signature (SrcByte + 3));   --00dddddd

         DstNum0 := SrcNum0*4 + (Srcnum1/16);   --aaaaaa00 + 000000bb = aaaaaabb
         DstNum1 := Srcnum1*16 + (SrcNum2/4);   --bbbb0000 + 0000cccc = bbbbcccc
         DstNum2 := SrcNum2*64 + SrcNum3;       --cc000000 + 00dddddd = ccdddddd

         Bytes(sigOffset + dstBytes) := DstNum0;
         Bytes(sigOffset + (dstBytes+1)) := DstNum1;
         Bytes(sigOffset + (dstBytes+2)) := DstNum2;

         SrcByte := SrcByte + 4;
         DstBytes := DstBytes + 3;
      end loop;

      -- Finally, we know how many bytes have been used on the wire (24 plus the
      -- length of the signer's name plus the length of the key)
      DstBytes := DNS_Types.Packet_Bytes_Range (24 + Current_Name_Length) +
        (DstBytes - DNS_Types.Packet_Bytes_Range (1));
      -- sets the out parameter of this procedure

      -- and we can set RDLength (2 bytes, value is 18 plus the length of the
      -- signer's name plus the length of the key)

      -- The things we do to make SPARK happy.
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       Unsigned_Types.Unsigned16
                         (From_Bytes_Range (DstBytes - 6) mod 65536));
      -- sets RDLength field (TTL and RDLength fields don't count, so subtract
      -- 4+2=6 bytes)
   end Set_TTL_Data_RRSig;

   procedure Set_TTL_Data_NS_Response
     (Bytes               : in out DNS_Types.Bytes_Array_Type;
      Start_Byte          : in     DNS_Types.Packet_Bytes_Range;
      NS_Record           : in     RR_Type.NS_Record_Type.NSRecordType;
      Current_Name_Length : in     RR_Type.WireStringTypeIndex) is
   begin
      -- TTL
      Set_Unsigned_32 (Bytes, Start_Byte, NS_Record.TTLInSeconds);
      -- DATA # bytes is equal to length of WireString
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       Unsigned_Types.Unsigned16 (Current_Name_Length));
      -- copy NS record
      for I in RR_Type.WireStringTypeIndex range 1 .. Current_Name_Length loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 6) -
                          DNS_Types.Packet_Bytes_Range
                            (Current_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last);

         Bytes ((Start_Byte + 5) + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (NS_Record.NameServer (I)));
      end loop;
   end Set_TTL_Data_NS_Response;

   procedure Set_TTL_Data_PTR_Response
     (Bytes               : in out DNS_Types.Bytes_Array_Type;
      Start_Byte          : in     DNS_Types.Packet_Bytes_Range;
      Ptr_Record          : in     RR_Type.Ptr_record_type.PtrRecordType;
      Current_Name_Length : in     RR_Type.WireStringTypeIndex)
   is
   begin
      -- TTL
      Set_Unsigned_32 (Bytes, Start_Byte, Ptr_Record.TTLInSeconds);
      -- DATA # bytes is equal to length of WireString
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       Unsigned_Types.Unsigned16 (Current_name_Length));
      -- copy NS record
      for I in RR_Type.WireStringTypeIndex range 1 .. Current_Name_Length loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 6) -
                          DNS_Types.Packet_Bytes_Range (Current_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last);
         Bytes ((Start_Byte + 5) + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (Ptr_Record.DomainName (I)));
      end loop;
   end Set_TTL_Data_Ptr_Response;

   procedure Set_TTL_Data_MX_Response
     (Bytes               : in out DNS_Types.Bytes_Array_Type;
      Start_Byte          : in     DNS_Types.Packet_Bytes_Range;
      MX_Record           : in     RR_Type.MX_Record_Type.MXRecordType;
      Current_Name_Length : in     RR_Type.WireStringTypeIndex)
   is
   begin
      -- TTL
      Set_Unsigned_32 (Bytes, Start_Byte, MX_Record.TTLInSeconds);
      -- DATA # bytes is equal to length of WireString + 2
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       Unsigned_Types.Unsigned16 (Current_Name_Length + 2));
      -- MAIL exchanger preference
      Set_Unsigned_16 (Bytes, Start_Byte + 6, MX_Record.Pref);
      -- copy NS record
      for I in RR_Type.WireStringTypeIndex range 1 .. Current_Name_Length loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 8) -
                          DNS_Types.Packet_Bytes_Range (Current_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last);
         Bytes ((Start_Byte + 7) + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (MX_Record.MailExchanger (I)));
      end loop;
   end Set_TTL_Data_MX_Response;

   procedure Set_TTL_Data_SRV_Response
     (Bytes               : in out DNS_Types.Bytes_Array_Type;
      Start_Byte          : in     DNS_Types.Packet_Bytes_Range;
      Srv_Record          : in     RR_Type.Srv_record_type.SrvRecordType;
      Current_Name_Length : in     RR_Type.WireStringTypeIndex)
   is
   begin
      -- TTL
      Set_Unsigned_32 (Bytes, Start_Byte, Srv_Record.TTLInSeconds);
      -- DATA # bytes is equal to length of WireString + 6
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       Unsigned_Types.Unsigned16 (Current_Name_Length + 6));
      -- Server preference
      Set_Unsigned_16 (Bytes, Start_Byte + 6, Srv_Record.Pref);
      -- Server weight
      Set_Unsigned_16 (Bytes, Start_Byte + 8, Srv_Record.Weight);
      -- Server port
      Set_Unsigned_16 (Bytes, Start_Byte + 10, Srv_Record.PortNum);
      -- copy NS record
      for I in RR_Type.WireStringTypeIndex range 1 .. Current_Name_Length loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 12) -
            DNS_Types.Packet_Bytes_Range (Current_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last);

         Bytes ((Start_Byte + 11) + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (Srv_Record.ServerName (I)));
      end loop;
   end Set_TTL_Data_Srv_Response;

   procedure Set_TTL_Data_SOA_Response
     (Bytes                  : in out DNS_Types.Bytes_Array_Type;
      Start_Byte             : in     DNS_Types.Packet_Bytes_Range;
      SOA_Record             : in     RR_Type.SOA_Record_Type.SOARecordType;
      Nameserver_Name_Length : in     RR_Type.WireStringTypeIndex;
      Mailbox_Name_Length    : in     RR_Type.WireStringTypeIndex)
   is
      Current_Byte : DNS_Types.Packet_Bytes_Range;
   begin
      -- TTL
      Set_Unsigned_32 (Bytes, Start_Byte, SOA_Record.TTLInSeconds);
      -- DATA # bytes is equal to length of both WireStrings + 20
      Set_Unsigned_16 (Bytes,
                       Start_Byte + 4,
                       Unsigned_Types.Unsigned16
                         (Nameserver_Name_Length + (Mailbox_Name_Length + 20)));
      -- copy NS record
      for I in RR_Type.WireStringTypeIndex
        range 1 .. Nameserver_Name_Length
      loop
         pragma Loop_Invariant
           (Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 20) -
                          DNS_Types.Packet_Bytes_Range
                            (Mailbox_Name_Length +
                             Nameserver_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last);
         Bytes ((Start_Byte + 5) + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (SOA_Record.NameServer (I)));
      end loop;
      Current_Byte := Start_Byte+DNS_Types.Packet_Bytes_Range
                        (5 + (Nameserver_Name_Length));
      -- copy MB record
      for I in RR_Type.WireStringTypeIndex range 1 .. Mailbox_Name_Length loop
         pragma Loop_Invariant
           (Current_Byte >= 1 and
            Current_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 20) -
                            DNS_Types.Packet_Bytes_Range
                              (Mailbox_Name_Length) and
            I >= RR_Type.WireStringTypeIndex'First and
            I <= RR_Type.WireStringTypeIndex'Last);
         Bytes (Current_Byte + DNS_Types.Packet_Bytes_Range (I)) :=
           DNS_Types.Byte (Character'Pos (SOA_Record.Email(I)));
      end loop;
      Current_Byte := Start_Byte + DNS_Types.Packet_Bytes_Range
                          (6 + (Nameserver_Name_Length + Mailbox_Name_Length));
      -- serial number
      Set_Unsigned_32 (Bytes, Current_Byte, SOA_Record.SerialNumber);
      -- refresh interval
      Set_Unsigned_32 (Bytes, Current_Byte + 4, SOA_Record.Refresh);
      -- retry interval
      Set_Unsigned_32 (Bytes, Current_Byte + 8, SOA_Record.Retry);
      -- expiration limit
      Set_Unsigned_32 (Bytes, Current_Byte + 12, SOA_Record.Expiry);
      -- minimum TTL
      Set_Unsigned_32 (Bytes, Current_Byte + 16, SOA_Record.Minimum);
   end Set_TTL_Data_SOA_Response;

   procedure Set_TTL_Data_AAAA_IP
     (Bytes       : in out DNS_Types.Bytes_Array_Type;
      Start_Byte  : in     DNS_Types.Packet_Bytes_Range;
      AAAA_Record : in     RR_Type.AAAA_Record_Type.AAAARecordType)
   is
   begin
      -- TTL
      Set_Unsigned_32 (Bytes, Start_Byte, AAAA_Record.TTLInSeconds);
      -- DATA 16 bytes
      Set_Unsigned_16(Bytes, Start_Byte + 4, 16);
      for I in RR_Type.AAAA_Record_Type.IPV6AddrTypeIndex loop
         -- IP address
         Set_Unsigned_16
           (Bytes,
            Start_Byte + DNS_Types.Packet_Bytes_Range
                           (6 + 2*(I -
                            RR_Type.AAAA_Record_Type.IPV6AddrTypeIndex'First)),
            AAAA_Record.IPV6 (I));
      end loop;
   end Set_TTL_Data_AAAA_IP;


   procedure Get_Query_Name_Type_Class
     (Input_Packet  : in     DNS_Types.DNS_Packet;
      Input_Bytes   : in     DNS_Types.Packet_Length_Range;
      DomainName    :    out RR_Type.WireStringType;
      Query_Type    :    out DNS_Types.Query_Type;
      Query_Class   :    out DNS_Types.Query_Class;
      End_Byte      :    out DNS_Types.Packet_Bytes_Range)
   is
      Byte : DNS_types.Packet_Bytes_Range := DNS_Types.Packet_Bytes_Range'First;
      I : Natural := RR_Type.WireStringType'First;
      QT_Natural, QC_Natural : Natural;

      function Type_To_Natural is new Ada.Unchecked_Conversion
        (DNS_Types.Query_Type, Natural);

      function To_Type is new Ada.Unchecked_Conversion
        (Natural, DNS_Types.Query_Type);

      function Class_To_Natural is new Ada.Unchecked_Conversion
        (DNS_Types.Query_Class, Natural);

      function To_Class is new Ada.Unchecked_Conversion
        (Natural, DNS_Types.Query_Class);
   begin
      DomainName := RR_Type.WireStringType'(others => ' ');
      while Integer (Byte) <= Integer (Input_Bytes - 5)
        and then Input_Packet.Bytes (Byte) /= 0
        and then I < RR_Type.WireStringType'Last
      loop
         pragma Loop_Invariant
           (I >= RR_Type.WireStringType'First and
            I < RR_Type.WireStringType'Last and
            Byte >= DNS_Types.Packet_Bytes_Range'First and
            Integer(Byte) <= Integer (Input_Bytes - 5));
         DomainName (I) := Character'Val (Input_Packet.Bytes (Byte));
         I := I + 1;
         Byte := Byte + 1;
      end loop;
      DomainName (I) := Character'Val (0);
--      for I in Byte-2..Byte+4 loop
--         Ada.Text_IO.Put_Line("byte: " & Dns_Types.Packet_Bytes_Range'Image(I) & ":" &
--            Natural'Image(natural(Input_Packet.Bytes(I))));
--      end loop;
      QT_Natural := Natural (Input_Packet.Bytes (Byte + 1))*256 +
                    Natural (Input_Packet.Bytes (Byte + 2));
      QC_Natural := Natural (Input_Packet.Bytes (Byte + 3))*256 +
                    Natural (Input_Packet.Bytes (Byte + 4));
--      ada.Text_IO.put_line("qt: " & natural'image(qt_natural));
--      ada.Text_IO.put_line("qc: " & natural'image(qc_natural));
      if QT_Natural >= Type_To_Natural (DNS_Types.Query_Type'First)
        and QT_Natural <= Type_To_Natural (DNS_Types.Query_Type'Last)
      then
         Query_Type := To_Type (QT_Natural);
         if not Query_Type'Valid then
            Query_Type := DNS_Types.Unimplemented;
         end if;
      else
         Query_Type := DNS_Types.Unimplemented;
      end if;

      if QC_Natural >= Class_To_Natural (DNS_Types.Query_Class'First)
        and QC_Natural <= Class_To_Natural (DNS_Types.Query_Class'Last)
      then
         Query_Class := To_Class (QC_Natural);
         if not Query_Class'Valid then
            Query_Class := DNS_Types.None_Class;
         end if;
      else
         Query_Class := DNS_Types.None_Class;
      end if;
      End_Byte := Byte + 4;
   end Get_Query_Name_Type_Class;

   procedure Create_Response_Error
     (Input_Bytes   : in     DNS_Types.Packet_Length_Range;
      Output_Packet : in out DNS_Types.DNS_Packet;
      Output_Bytes  :    out DNS_Types.Packet_Length_Range)
   is
   begin
      Output_Packet.Header.AA := True;
      Output_Packet.Header.RCode   := DNS_Types.Not_Implemented;
      Output_Packet.Header.ANCount := 0;
      Output_Bytes := Input_Bytes;
   end Create_Response_Error;

   procedure Create_Response_AAAA
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   is
      Current_Byte        : DNS_Types.Packet_Bytes_Range;
      ReturnedAAAARecords : RR_Type.AAAA_Record_Type.AAAARecordBucketType;
      NumFound            : Natural;
      Response_Counter    : Natural;
      NumAFound           : Natural;
   begin
      DNS_Table_Pkg.DNS_Table.QueryAAAARecords
        (DomainName      => DomainName,
         ReturnedRecords => ReturnedAAAARecords,
         HowMany         => NumFound);

      Current_Byte := Start_Byte;

      if NumFound >= 1 then
         Response_Counter := 1;
         while Response_Counter <= NumFound
           and Integer (Current_Byte) < DNS_Types.Packet_Size -
                                        (28 + DNS_Types.Header_Bits/8)
         loop
            pragma Loop_Invariant
              (Response_Counter >= 1 and
               Response_Counter <= NumFound and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
                               DNS_types.Unsigned_Short
                                 (RR_Type.MaxNumRecords) and
               Current_Byte = Start_Byte +
                              DNS_Types.Packet_Bytes_Range
                                (28 * (Response_Counter - 1)) and
               Integer(Current_Byte) < DNS_Types.Packet_Size -
                                         (28 + DNS_Types.Header_Bits/8) and
               NumFound <= RR_Type.MaxNumRecords);

            -- Ptr to character of message
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- AAAA
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#1C#;
            -- IN
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            Set_TTL_Data_AAAA_IP (Output_Packet.Bytes,
                                  Current_Byte + 7,
                                  ReturnedAAAARecords
                                    (ReturnedAAAARecords'First +
                                       (Response_Counter - 1)));
            Response_Counter := Response_Counter + 1;
            Current_Byte := Current_Byte + 28;
         end loop;
         --Output_Bytes := Input_Bytes +
         --                DNS_Types.Packet_Length_Range
         --                  (28*(Response_Counter-1));
      else
         DNS_Table_Pkg.DNS_Table.CountARecords (DomainName => DomainName,
                                                HowMany    => NumAFound);
         if NumAFound > 0 then
            Output_Packet.Header.AA := True;
         end if;
      end if;

      Output_Bytes := DNS_Types.Packet_Length_Range
                        (Current_Byte +
                         DNS_Types.Packet_Bytes_Range
                           (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (NumFound);
   end Create_Response_AAAA;

   procedure Create_Response_A
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   is
      Current_Byte     : DNS_Types.Packet_Bytes_Range;
      ReturnedARecords : RR_Type.A_Record_Type.ARecordBucketType;
      NumFound         : Natural;
      Response_Counter : Natural;
      NumAAAAFound     : Natural;
   begin
      DNS_Table_Pkg.DNS_Table.QueryARecords
        (DomainName      => DomainName,
         ReturnedRecords => ReturnedARecords,
         HowMany         => NumFound);

      Current_Byte := Start_Byte;

      if NumFound>=1 then
         Response_Counter := 1;
         while Response_Counter <= NumFound
           and Integer(Current_Byte) < DNS_Types.Packet_Size -
                                       (16 + DNS_Types.Header_Bits/8)
         loop
            pragma Loop_Invariant
              (Response_Counter >= 1 and
               Response_Counter <= NumFound and
               Integer (Start_Byte) <= DNS_Types.Packet_Size and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
                               DNS_types.Unsigned_Short
                                 (RR_Type.MaxNumRecords) and
               Current_Byte = Start_Byte + DNS_Types.Packet_Bytes_Range
                                             (16 * (Response_Counter - 1)) and
               Integer (Current_Byte) < DNS_Types.Packet_Size -
                                          (16 + DNS_Types.Header_Bits/8) and
               Numfound <= RR_Type.MaxNumRecords);

            -- Ptr to character of message
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- A
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#01#;
            -- IN
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            Set_TTL_Data_IP
              (Output_Packet.Bytes,
               Current_Byte + 7,
               ReturnedARecords (ReturnedARecords'First +
                                   (Response_Counter - 1)));
            Response_Counter := Response_Counter + 1;
            Current_Byte := Current_Byte + 16;
         end loop;
         --Output_Bytes := Input_Bytes + DNS_Types.Packet_Length_Range
         --                                (16*(Response_Counter - 1));
      else
         DNS_Table_Pkg.DNS_Table.CountAAAARecords
           (DomainName => DomainName,
            HowMany    => NumAAAAFound);
         if NumAAAAFound > 0 then
            Output_Packet.Header.AA := True;
         end if;
      end if;
      Output_Bytes := DNS_Types.Packet_Length_Range
                        (Current_Byte +
                         DNS_Types.Packet_Bytes_Range
                           (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short(numFound);
   end Create_Response_A;

   --DNSSec code here {DNSKey, NSec, RRSig}  --BSF
   procedure Create_Response_DNSKey
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   is
      Current_Byte          : DNS_Types.Packet_Bytes_Range;
      ReturnedDNSKeyRecords : RR_Type.DNSKey_Record_Type.DNSKeyRecordBucketType;
      NumFound              : Natural;
      Response_Counter      : Natural;
      CurrentRec            : RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      bytesUsedInEncodedKey : RR_type.DNSKey_Record_Type.KeyLengthValueType;
   begin
      DNS_Table_Pkg.DNS_Table.QueryDNSKeyRecords
        (DomainName      => DomainName,
         ReturnedRecords => ReturnedDNSKeyRecords,
         HowMany         => NumFound);
      Current_Byte := Start_Byte;
      -- actually the last byte of the question section

      if NumFound >= 1 then
         Response_Counter := 1;
         CurrentRec := ReturnedDNSKeyRecords (Response_Counter);
         --loop to build the return message
         while Response_Counter <= NumFound
           and Integer (Current_Byte) <
                 DNS_Types.Packet_Size -
                 ((16 + RR_Type.DNSKey_Record_Type.MaxDNSKeyLength) +
                 DNS_Types.Header_Bits/8)
         loop
            pragma Loop_Invariant
              (Response_Counter >= 1 and
               Response_Counter <= NumFound and
               Integer (Start_Byte) <= DNS_Types.Packet_Size and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
                               DNS_Types.Unsigned_Short
                                 (RR_Type.MaxNumRecords) and
               Integer (Current_Byte) < DNS_Types.Packet_Size -
                 (16 + RR_Type.DNSKey_Record_Type.MaxDNSKeyLength +
                    DNS_Types.Header_Bits/8) and
               NumFound <= RR_Type.MaxNumRecords);
            -- NAME (2 bytes, PTR to name)
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- TYPE (2 bytes, DNSKEY --> 48)
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#30#;
            -- CLASS (2 bytes, IN --> 1)
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            --set TTL (4 bytes), RDLENGTH (2 bytes) and
            --RDATA (4 bytes + keylength) fields
            Set_TTL_Data_DNSKey
              (Output_Packet.Bytes,
               Current_Byte + 7,
               CurrentRec,
               BytesUsedInEncodedKey);
            Current_Byte := Current_Byte +
                            DNS_Types.Packet_Bytes_Range
                              (16 + bytesUsedInEncodedKey);
            Response_Counter := Response_Counter + 1;
            if Response_Counter <= NumFound then
               CurrentRec := ReturnedDNSKEYRecords(Response_Counter);
            end if;
         end loop;
      end if; --NumFound >= 1
      Output_Bytes := DNS_Types.Packet_Length_Range
                        (Current_Byte +
                         DNS_Types.Packet_Bytes_Range
                           (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (NumFound);
   end Create_Response_DNSKey;

   procedure Create_Response_NSec
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      QName_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   is
      Current_Byte        : DNS_Types.Packet_Bytes_Range;
      ReturnedNSecRecords : RR_Type.NSEC_Record_Type.NSecRecordBucketType;
      NumFound            : Natural;
      Response_Counter    : Natural;
      CurrentRec          : RR_Type.NSec_Record_Type.NSecRecordType;
      bytesUsedInRRData   : DNS_Types.Packet_Length_Range;
   begin
      DNS_Table_Pkg.DNS_Table.QueryNSecRecords
        (DomainName      => DomainName,
         ReturnedRecords => ReturnedNSecRecords,
         HowMany         => NumFound);
      Current_Byte := Start_Byte; -- actually the last byte of the question
                                  -- section
      if NumFound >= 1 then
         Response_Counter := 1;
         CurrentRec := ReturnedNSecRecords (Response_Counter);
         while Response_Counter <= NumFound
           and Integer (Current_Byte) <
                 DNS_Types.Packet_Size -
                 ((((12 + RR_Type.NSec_Record_Type.MaxRRDataLength) +
                    RR_Type.MaxDomainNameLength) + 1) + DNS_Types.Header_Bits/8)
         loop
            -- NAME (2 bytes, Ptr to name)
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- TYPE (2 bytes, NSec --> 47)
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#2f#;
            -- CLASS (2 bytes, IN --> 1)
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            --set TTL (4 bytes), RDLENGTH (2 bytes) and RDATA (domainNameLength
            --+ rrListLength) fields
            Set_TTL_Data_NSec (Output_Packet.Bytes,
                               Current_Byte + 7,
                               CurrentRec,
                               BytesUsedInRRData);

            pragma Loop_Invariant
              (Response_Counter >= 1 and
               Response_Counter <= NumFound and
               Integer (Start_Byte) <= DNS_Types.Packet_Size and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
                               DNS_types.Unsigned_Short
                                 (RR_Type.MaxNumRecords) and
               Integer (Current_Byte) <
                 DNS_Types.Packet_Size -
                 ((12 + RR_Type.NSec_Record_Type.MaxRRDataLength) +
                  (RR_Type.MaxDomainNameLength + 1) +
                  DNS_Types.Header_Bits/8) and
               BytesUsedInRRData <=
                 DNS_Types.Packet_Length_Range
                   (RR_Type.NSec_Record_Type.MaxRRDataLength) and
               NumFound <= RR_Type.MaxNumRecords);

            Current_Byte :=
              Current_Byte + DNS_Types.Packet_Bytes_Range
                               (12 + BytesUsedInRRData);

            Response_Counter := Response_Counter + 1;
            if Response_Counter <= NumFound then
               CurrentRec := ReturnedNSecRecords (Response_Counter);
            end if;
         end loop;
      end if; --NumFound >= 1
      Output_Bytes :=
        DNS_Types.Packet_Length_Range
          (Current_Byte +
           DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (NumFound);
   end Create_Response_NSec;

   procedure Create_Response_RRSig
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      QName_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   is
      Current_Byte         : DNS_Types.Packet_Bytes_Range;
      ReturnedRRSigRecords : RR_Type.RRSig_Record_Type.RRSigRecordBucketType;
      NumFound             : Natural;
      Response_Counter     : Natural;
      CurrentRec           : RR_Type.RRSig_Record_Type.RRSigRecordType;
      BytesUsedOnWire      : DNS_Types.Packet_Bytes_Range;
   begin
      DNS_Table_Pkg.DNS_Table.QueryRRSigRecords
        (DomainName      => DomainName,
         ReturnedRecords => ReturnedRRSigRecords,
         HowMany         => NumFound);
      Current_Byte := Start_Byte; -- actually the last byte of the question
                                  -- section
      if NumFound >= 1 then
         Response_Counter := 1;
         CurrentRec := ReturnedRRSigRecords (Response_Counter);
         --loop to build the return message
         while Response_Counter <= NumFound
           and Integer (Current_Byte) <
                 DNS_Types.Packet_Size -
                 (((30 + RR_Type.MaxDomainNameLength) +
                   RR_Type.RRSig_Record_Type.MaxRRSigLength) +
                  DNS_Types.Header_Bits/8)
         loop
            pragma Loop_Invariant
              (Response_Counter >= 1 and
               Response_Counter <= NumFound and
               Integer (Start_Byte) <= DNS_Types.Packet_Size and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
                               DNS_types.Unsigned_Short
                                 (RR_Type.MaxNumRecords) and
               Integer (Current_Byte) <
                 DNS_Types.Packet_Size -
                 (((30 + Rr_Type.MaxDomainNameLength) +
                   RR_Type.RRSig_Record_Type.maxrrsigLength) +
                  DNS_Types.Header_Bits/8) and
               NumFound <= RR_Type.MaxNumRecords);
            -- NAME (2 bytes, Ptr to name)
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- TYPE (2 bytes, DNSKey --> 46)
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#2E#;
            -- CLASS (2 bytes, IN --> 1)
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            --set TTL (4 bytes), RDLength (2 bytes) and RData
            --(18 bytes + name length + sig length) fields
            Set_TTL_Data_RRSig
              (Output_Packet.Bytes,
               Current_Byte + 7,
               CurrentRec,
               BytesUsedOnWire);
            Current_Byte := (Current_Byte + 6) + BytesUsedOnWire;
            Response_Counter := Response_Counter + 1;
            if Response_Counter <= NumFound then
               CurrentRec := ReturnedRRSigRecords (Response_Counter);
            end if;
         end loop;
      end if; --NumFound >= 1
      Output_Bytes :=
        DNS_Types.Packet_Length_Range (Current_Byte +
                                       DNS_Types.Packet_Bytes_Range
                                         (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (NumFound);
   end Create_Response_RRSig;

   procedure Create_Response_NS
     (Start_Byte      : in     DNS_Types.Packet_Bytes_Range;
      DomainName      : in     RR_Type.WireStringType;
      Num_Found       :    out RR_Type.NumberOfRecordsType;
      QName_Location  : in     DNS_Types.QName_Ptr_Range;
      QName_Locations :    out QName_Ptr_Range_Array;
      Replies         :    out RR_Type.NS_Record_Type.NSRecordBucketType;
      Output_Packet   : in out DNS_Types.DNS_Packet;
      Answer_Count    : in out DNS_Types.Unsigned_Short;
      Output_Bytes    :    out DNS_Types.Packet_Length_Range)
   is
      Response_Counter    : Natural;
      Current_Byte        : DNS_Types.Packet_Bytes_Range;
      Current_Name_Length : RR_Type.WireStringTypeIndex;
   begin
      QName_Locations := QName_Ptr_Range_Array'(others => 0);
      Current_Byte := Start_Byte;
      DNS_Table_Pkg.DNS_Table.QueryNSRecords
        (DomainName      => DomainName,
         ReturnedRecords => Replies,
         HowMany         => Num_Found);
      if Num_Found >= 1 then
         Response_Counter := 1;
         Current_Name_Length :=
           RR_Type.WireNameLength (Replies (Response_Counter).NameServer);

         while Response_Counter <= Num_Found
           and then Integer (Current_Byte) <
                      (DNS_Types.Packet_Size - (12 + DNS_Types.Header_Bits/8))-
                      Current_Name_Length
         loop
            pragma Loop_Invariant
              (Response_Counter >=1 and
               Response_Counter <= Num_Found and
               Current_Name_Length >=1 and
               Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
               Num_Found <= RR_Type.MaxNumRecords and
               Integer (Start_Byte) <= DNS_Types.Packet_Size and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
               DNS_Types.Unsigned_Short (RR_Type.MaxNumRecords) and
               Integer(Current_Byte) < (DNS_Types.Packet_Size -
                                        (12+DNS_Types.Header_Bits/8)) -
                                       (Current_Name_Length) and
               Current_Byte >= 0);
            -- Ptr to character of message
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- NS
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#02#;
            -- IN
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            QName_Locations (Response_Counter) :=
              DNS_Types.QName_Ptr_Range
              ((Current_Byte+12) +
               DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
            Set_TTL_Data_NS_Response
              (Output_Packet.Bytes,
               Current_Byte + 7,
               Replies (Response_Counter),
               Current_Name_Length);
            Response_Counter := Response_Counter + 1;
            Current_Byte := (Current_Byte + 12) +
                            DNS_Types.Packet_Bytes_Range (Current_Name_Length);
            if Response_Counter <= Num_Found then
               Current_Name_Length :=
                 RR_Type.WireNameLength (Replies (Response_Counter).NameServer);
            end if;
         end loop;
      end if;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range
          (Current_Byte +
           DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (Num_Found);
   end Create_Response_NS;

   procedure Create_Response_Ptr
     (Start_Byte      : in     DNS_Types.Packet_Bytes_Range;
      DomainName      : in     RR_Type.WireStringType;
      QName_Location  : in     DNS_Types.QName_Ptr_Range;
      Output_Packet   : in out DNS_Types.DNS_Packet;
      Answer_Count    : in out DNS_Types.Unsigned_Short;
      Output_Bytes    :    out DNS_Types.Packet_Length_Range)
   is
      Num_Found           : RR_Type.NumberOfRecordsType;
      Response_Counter    : Natural;
      Current_Byte        : DNS_Types.Packet_Bytes_Range;
      Current_Name_Length : RR_Type.WireStringTypeIndex;
      Replies             : RR_Type.Ptr_record_type.PtrRecordBucketType;
   begin
      Current_Byte := Start_Byte;
      DNS_Table_Pkg.DNS_Table.QueryPtrRecords
        (DomainName      => DomainName,
         ReturnedRecords => Replies,
         HowMany         => Num_Found);
      if Num_Found >= 1 then
         Response_Counter := 1;
         Current_Name_Length :=
           RR_Type.WireNameLength (Replies (Response_Counter).DomainName);
         while Response_Counter <= Num_Found
           and then Integer (Current_Byte) <
                      (DNS_Types.Packet_Size - (12+DNS_Types.Header_Bits/8))-
                      Current_Name_Length
         loop
            pragma Loop_Invariant
              (Response_Counter >= 1 and
               Response_Counter <= Num_Found and
               Current_Name_Length >= 1 and
               Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
               Num_Found <= RR_Type.MaxNumRecords and
               Integer (Start_Byte) <= DNS_Types.Packet_Size and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
                               DNS_types.Unsigned_Short
                                 (RR_Type.MaxNumRecords) and
               Integer (Current_Byte) <
                 (DNS_Types.Packet_Size - (12 + DNS_Types.Header_Bits/8)) -
                 Current_Name_Length and
               Current_Byte >= 0);
            -- PTR to character of message
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- PTR
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#0C#;
            -- IN
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            Set_TTL_Data_Ptr_Response
              (Output_Packet.Bytes,
               Current_Byte + 7,
               Replies (Response_Counter),
               Current_Name_Length);
            Response_Counter := Response_Counter + 1;
            Current_Byte := (Current_Byte + 12) +
                            DNS_Types.Packet_Bytes_Range (Current_Name_Length);
            if Response_Counter <= Num_Found then
               Current_Name_Length :=
                 RR_Type.WireNameLength (Replies (Response_Counter).DomainName);
            end if;
         end loop;
      end if;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range (Current_Byte +
                                       DNS_Types.Packet_Bytes_Range
                                         (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (Num_Found);
   end Create_Response_Ptr;

   procedure Create_Response_MX
     (Start_Byte      : in     DNS_Types.Packet_Bytes_Range;
      DomainName      : in     RR_Type.WireStringType;
      Num_Found       :    out RR_Type.NumberOfRecordsType;
      QName_Location  : in     DNS_Types.QName_Ptr_Range;
      QName_Locations :    out QName_Ptr_Range_Array;
      Replies         :    out RR_Type.MX_Record_Type.MXRecordBucketType;
      Output_Packet   : in out DNS_Types.DNS_Packet;
      Answer_Count    : in out DNS_Types.Unsigned_Short;
      Output_Bytes    :    out DNS_Types.Packet_Length_Range)
   is
      Response_Counter    : Natural;
      Current_Byte        : DNS_Types.Packet_Bytes_Range;
      Current_Name_Length : RR_Type.WireStringTypeIndex;
   begin
      QName_Locations := QName_Ptr_Range_Array'(others => 0);
      Current_Byte := Start_Byte;
      DNS_Table_Pkg.DNS_Table.QueryMXRecords
        (DomainName      => DomainName,
         ReturnedRecords => Replies,
         HowMany         => Num_Found);
      if Num_Found >= 1 then
         Response_Counter := 1;
         Current_Name_Length :=
           RR_Type.WireNameLength (Replies (Response_Counter).MailExchanger);
         while Response_Counter <= Num_Found
           and then Integer(Current_Byte) <
                      (DNS_Types.Packet_Size - (14 + DNS_Types.Header_Bits/8))-
                      Current_Name_Length
         loop
            pragma Loop_Invariant
              (Response_Counter >= 1 and
               Response_Counter <= Num_Found and
               Current_Name_Length >= 1 and
               Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
               Num_Found <= RR_Type.MaxNumRecords and
               Integer (Start_Byte) <= DNS_Types.Packet_Size and
               Answer_Count = Answer_Count'Loop_Entry and
               Answer_Count <= DNS_Types.Unsigned_Short'Last -
                               DNS_Types.Unsigned_Short
                                 (RR_Type.MaxNumRecords) and
               Integer (Current_Byte) <
                 (DNS_Types.Packet_Size - (14 + DNS_Types.Header_Bits/8))-
                 Current_Name_Length and
               Current_Byte >= 0);
            -- Ptr to character of message
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- MX
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#0F#;
            -- IN
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            QName_Locations(Response_Counter) :=
              DNS_Types.QName_Ptr_Range
                ((Current_Byte + 14) +
                 DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
            Set_TTL_Data_MX_Response
              (Output_Packet.Bytes,
               Current_Byte + 7,
               Replies (Response_Counter),
               Current_Name_Length);
            Response_Counter := Response_Counter + 1;
            Current_Byte :=
              (Current_Byte + 14) +
              DNS_Types.Packet_Bytes_Range (Current_Name_Length);
            if Response_Counter <= Num_Found then
               Current_Name_Length :=
                 RR_Type.WireNameLength
                   (Replies (Response_Counter).MailExchanger);
            end if;
         end loop;
      end if;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range
          (Current_Byte +
           DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short(Num_Found);
   end Create_Response_MX;

   procedure Create_Response_SRV(
         Start_Byte      : in DNS_Types.Packet_Bytes_Range;
         DomainName      : in RR_Type.WireStringType;
         Num_Found       : out RR_Type.NumberOfRecordsType;
         Qname_Location  : in DNS_Types.QNAME_PTR_RANGE;
         Qname_Locations : out QNAME_PTR_RANGE_Array;
         Replies         : out RR_Type.srv_record_type.SRVRecordBucketType;
         Output_Packet   : in out DNS_Types.DNS_Packet;
         Answer_Count    : in out DNS_Types.Unsigned_Short;
         Output_Bytes    : out DNS_Types.Packet_Length_Range) is
      Response_Counter : Natural;
      Current_Byte  : DNS_Types.Packet_Bytes_Range;
      Current_Name_Length : RR_Type.WireStringTypeIndex;
   begin
      QName_Locations := QName_Ptr_Range_Array'(others => 0);
      Current_Byte := Start_Byte;
      DNS_Table_Pkg.DNS_Table.QuerySrvRecords
        (DomainName      => DomainName,
         ReturnedRecords => Replies,
         HowMany         => Num_Found);
      if Num_Found >= 1 then
         Response_Counter := 1;
         Current_Name_Length :=
           RR_Type.WireNameLength (Replies (Response_Counter).ServerName);
         while Response_Counter <= Num_Found
           and then Integer (Current_Byte) <
                      (DNS_Types.Packet_Size - (18 + DNS_Types.Header_Bits/8)) -
                      Current_Name_Length
         loop
            pragma Loop_Invariant
              (Response_Counter >= 1 and
                 Response_Counter <= Num_Found and
                 Current_Name_Length >= 1 and
                 Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
                 Num_Found <= RR_Type.MaxNumRecords and
                 Integer (Start_Byte) <= DNS_Types.Packet_Size and
                 Answer_Count = Answer_Count'Loop_Entry and
                 Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                 DNS_types.Unsigned_Short
                                   (RR_Type.MaxNumRecords) and
                 Integer (Current_Byte) < (DNS_Types.Packet_Size -
                                             (18 + DNS_Types.Header_Bits/8)) -
                                          Current_Name_Length and
                 Current_Byte >= 0);
            -- PTR to character of message
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- SRV
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#21#;
            -- IN
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            Qname_Locations (Response_Counter) :=
              DNS_Types.QName_Ptr_Range
                ((Current_Byte + 18) +
                 DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
            -- offset = 18

            Set_TTL_Data_Srv_Response
              (Output_Packet.Bytes,
               Current_Byte + 7,
               Replies (Response_Counter),
               Current_Name_Length);
            Response_Counter := Response_Counter + 1;
            Current_Byte :=
              (Current_Byte + 18) +
              DNS_Types.Packet_Bytes_Range (Current_Name_Length);
            --  offset = 18

            if Response_Counter <= Num_Found then
               Current_Name_Length :=
                 RR_Type.WireNameLength (Replies (Response_Counter).ServerName);
            end if;
         end loop;
      end if;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range
          (Current_Byte +
           DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (Num_Found);
   end Create_Response_Srv;

   procedure Create_Response_SOA
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      QName_Location : in     DNS_Types.QNAME_PTR_RANGE;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   is
      Response_Counter       : Natural;
      Current_Byte           : DNS_Types.Packet_Bytes_Range;
      Nameserver_Name_Length : RR_Type.WireStringTypeIndex;
      Mailbox_Name_Length    : RR_Type.WireStringTypeIndex;
      Num_Found              : RR_Type.NumberOfRecordsType;
      Replies                : RR_Type.SOA_Record_Type.SOARecordBucketType;
   begin
      Current_Byte := Start_Byte;
      DNS_Table_Pkg.DNS_Table.QuerySOARecords
        (DomainName      => DomainName,
         ReturnedRecords => Replies,
         HowMany         => Num_Found);
      if Num_Found >= 1 then
         Response_Counter := 1;
         Nameserver_Name_Length :=
           RR_Type.WireNameLength (Replies (Response_Counter).Nameserver);

         Mailbox_Name_Length :=
           RR_Type.WireNameLength (Replies (Response_Counter).Email);

         if Integer (Current_Byte) < (DNS_Types.Packet_Size -
                                      (32 + DNS_Types.Header_Bits/8))-
                                     (Nameserver_Name_Length +
                                      Mailbox_Name_Length)
         then
            -- PTR to character of message
            Set_Unsigned_16
              (Output_Packet.Bytes,
               Current_Byte + 1,
               Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
            -- SOA
            Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 4) := 16#06#;
            -- IN
            Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
            Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
            Set_TTL_Data_SOA_Response
              (Output_Packet.Bytes,
               Current_Byte + 7,
               Replies (Response_Counter),
               Nameserver_Name_Length,
               Mailbox_Name_Length);
            Current_Byte := (Current_Byte + 32) +
                            DNS_Types.Packet_Bytes_Range
                              (Nameserver_Name_Length + Mailbox_Name_Length);
         end if;
      end if;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range (Current_Byte +
                                       DNS_Types.Packet_Bytes_Range
                                         (DNS_Types.Header_Bits/8));
      Answer_Count := Answer_Count + DNS_Types.Unsigned_Short (Num_Found);
   end Create_Response_SOA;

   procedure Process_Response_CName
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      CNames         : in     RR_Type.CName_Record_Type.CNameRecordBucketType;
      DomainName     :    out RR_Type.WireStringType;
      QName_Location : in out DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   is
      Current_Byte : DNS_Types.Packet_Bytes_Range;
      Name_Length  : RR_Type.WireStringTypeIndex;
      I            : RR_Type.WireStringTypeIndex;
   begin
      --      CNames (CNames'First).CanonicalDomainName :=
      --        Character'Val (8) & "carlisle" & Character'Val (4) &
      --        "dfcs" & Character'Val (5) & "usafa" & Character'Val (3) &
      --        "edu" & Character'Val (0) & "       ";
      Current_Byte := Start_Byte;
      DomainName := CNames (CNames'First).CanonicalDomainName;
      Name_Length :=
        RR_Type.WirenameLength (CNames (CNames'First).CanonicalDomainName);
      if Integer (Current_Byte) < DNS_Types.Packet_Size -
                                  (12 + DNS_Types.Header_Bits/8)
      then
         -- Ptr to character of message
         Set_Unsigned_16
           (Output_Packet.Bytes,
            Current_Byte + 1,
            Unsigned_Types.Unsigned16 (QName_Location) + 16#C000#);
         -- CName
         Output_Packet.Bytes (Current_Byte + 3) := 16#00#;
         Output_Packet.Bytes (Current_Byte + 4) := 16#05#;
         -- IN
         Output_Packet.Bytes (Current_Byte + 5) := 16#00#;
         Output_Packet.Bytes (Current_Byte + 6) := 16#01#;
         -- TTL
         Set_Unsigned_32
           (Output_Packet.Bytes,
            Current_Byte + 7,
            CNames (CNames'First).TTLInSeconds);
         Set_Unsigned_16
           (Output_Packet.Bytes,
            Current_Byte + 11,
            Unsigned_Types.Unsigned16 (Name_Length));
         Current_Byte := Current_Byte + 12;
      end if;
      QName_Location :=
        DNS_Types.QName_Ptr_Range ((Integer(Current_Byte)) +
        DNS_Types.Header_Bits/8);
      I := 1;
      while I <= Name_Length
        and I < RR_Type.WireStringTypeIndex'Last
        and Integer (Current_Byte) + DNS_Types.Header_Bits/8 <
              DNS_Types.Packet_Size
      loop
         pragma Loop_Invariant
           (I < RR_Type.WireStringTypeIndex'Last and
            I <= Name_Length and
            Output_Packet.Header.ANCount = 0 and
            Current_Byte >= Start_Byte and
            Integer (Current_Byte) + DNS_Types.Header_Bits/8 <
              DNS_Types.Packet_Size);
         Current_Byte := Current_Byte + 1;
         Output_Packet.Bytes (Current_Byte) :=
           DNS_Types.Byte
             (Character'Pos (CNames (CNames'First).CanonicalDomainName (I)));
         I := I + 1;
      end loop;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range (Current_Byte +
                                       DNS_Types.Packet_Bytes_Range
                                         (DNS_Types.Header_Bits/8));
      Output_Packet.Header.ANCount := Output_Packet.Header.ANCount + 1;
   end Process_Response_CName;

   procedure Trim_Name
     (DomainName         : in     RR_Type.WireStringType;
      Trimmed_name       :    out RR_Type.WireStringType;
      QName_Location     : in     DNS_Types.QName_Ptr_Range;
      New_QName_Location :    out DNS_Types.QName_Ptr_Range)
   is
      Zone_Length : Natural;
   begin
      Zone_Length :=
        Natural (Character'Pos (DomainName (DomainName'First)) + 1);
      Trimmed_Name := RR_Type.WireStringType'(others => ' ');
      New_QName_Location := QName_Location;
      if Zone_Length > 0
        and Zone_Length < RR_Type.WireStringTypeIndex'Last
      then
         New_QName_Location := New_QName_Location +
                               DNS_Types.QName_Ptr_Range (Zone_Length);
         -- the assertion below is kind of interesting b/c we need to tell
         -- SPARK that zone_Length hasn't changed, and I don't really use it
         -- in the loop
         for I in RR_Type.WireStringTypeIndex
           range 1 .. RR_Type.WireStringTypeIndex'Last -
                     Natural (Character'Pos (DomainName (DomainName'First)) + 1)
         loop
            pragma Loop_Invariant
              (I + Zone_Length <= RR_Type.WireStringTypeIndex'Last and
               I >= 1 and
               Zone_Length =
                 Natural (Character'Pos (DomainName (DomainName'First))+1));
            Trimmed_Name (I) :=
              DomainName (I +
                          Natural (Character'Pos
                                     (DomainName (DomainName'First)) + 1));
         end loop;
      end if;
   end Trim_Name;

   procedure Create_NXDomain_Response
     (Start_Byte      : in     DNS_Types.Packet_Bytes_Range;
      DomainName      : in     RR_Type.WireStringType;
      QName_Location  : in     DNS_Types.QName_Ptr_Range;
      Output_Packet   : in out DNS_Types.DNS_Packet;
      Output_Bytes    :    out DNS_Types.Packet_Length_Range)
   is
      Answer_Count           : DNS_Types.Unsigned_Short := 0;
      Amount_Trimmed         : Natural := 0;
      Trimmed_Name           : RR_Type.WireStringType;
      Current_Name           : RR_Type.WireStringType;
      Current_QName_Location : DNS_Types.QName_Ptr_Range;
      New_QName_Location     : DNS_Types.QName_Ptr_Range;
   begin
      Current_QName_Location := QName_Location;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range
          (Start_Byte + DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
      Current_Name := DomainName;
      Output_Packet.Header.RCode   := DNS_Types.Name_Error;
      Output_Packet.Header.ANCount := 0;

      -- Amount_Trimmed is used to guarantee we don't end up in an infinite loop
      while Answer_Count=0
        and Amount_Trimmed < RR_Type.WireStringType'Last
        and Natural (Character'Pos (Current_Name (Current_Name'First)))/=0
        and Current_QName_Location <= DNS_Types.QName_Ptr_Range (Output_Bytes)
      loop
         pragma Loop_Invariant
           (Answer_Count = 0 and
            Amount_Trimmed >= 0 and
            Amount_Trimmed < RR_Type.WireStringType'Last and
            Output_Bytes <= DNS_Types.Packet_Length_Range'Last and
            Current_QName_Location <= DNS_Types.QName_Ptr_Range (Output_Bytes));
         Trim_Name
           (DomainName         => Current_Name,
            Trimmed_Name       => Trimmed_Name,
            QName_Location     => Current_QName_Location,
            New_QName_Location => New_QName_Location);
         Create_Response_SOA
           (Start_Byte      => Start_Byte,
            DomainName      => Trimmed_Name,
            Qname_Location  => New_QName_Location,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);
         Current_Name := Trimmed_Name;
         Current_QName_Location := New_QName_Location;
         Amount_Trimmed :=
           Amount_Trimmed +
           Natural (Character'Pos (DomainName (DomainName'First))+1);
      end loop;
      if Answer_Count >= 1 then
         Output_Packet.Header.AA := True;
      end if;
      Output_Packet.Header.NSCount := Answer_Count;
   end Create_NXDomain_Response;

   -- if we get in an EDNS option, we will add a response in kind
   procedure Create_Response_EDNS
     (Input_Packet       : in DNS_Types.DNS_Packet;
      Input_Bytes        : in DNS_Types.Packet_Length_Range;
      Query_End_Byte     : in DNS_Types.Packet_Bytes_Range;
      Start_Byte         : in DNS_Types.Packet_Bytes_Range;
      Output_Packet      : in out DNS_Types.DNS_Packet;
      Output_Bytes       : out DNS_Types.Packet_Length_Range;
      Additional_Count   : in out DNS_Types.Unsigned_Short;
      DNSSEC             : out Boolean;
      Max_Transmit       : out DNS_Types.Packet_Length_Range)
   is
      EDNS_Rec : DNS_Types.EDNS_Record;
      function To_Query_Type is new Ada.Unchecked_Conversion
        (DNS_Types.Unsigned_Short, DNS_Types.Query_Type);

      function From_Query_Type is new Ada.Unchecked_Conversion
        (DNS_Types.Query_Type, DNS_Types.Unsigned_Short);
   begin
      Max_Transmit := DNS_Types.UDP_Max_Size;
      Output_Bytes :=
        DNS_Types.Packet_Length_Range (Start_Byte +
                                       DNS_Types.Packet_Bytes_Range
                                         (DNS_Types.Header_Bits/8));
      DNSSec := False;

      -- if there's more to the packet, check for the OPT code
      if (Integer (Query_End_Byte) + 11) + (DNS_Types.Header_Bits/8) <=
           Integer (Input_Bytes)
        and (Integer (Start_Byte) + 11) + (DNS_Types.Header_Bits/8) <
           DNS_Types.Packet_Size
      then
         EDNS_Rec.Root    :=
           Character'Val (Input_Packet.Bytes (Query_End_Byte + 1));

         EDNS_Rec.Code    :=
           To_Query_Type
             (DNS_Types.Unsigned_Short
                (Input_Packet.Bytes (Query_End_Byte + 2))*256 +
              DNS_Types.Unsigned_Short
                (Input_Packet.Bytes (Query_End_Byte + 3)));
         if EDNS_Rec.Root = Character'Val(0)
           and EDNS_Rec.Code = DNS_Types.Opt
         then
            EDNS_Rec.Payload_Size :=
              DNS_Types.Unsigned_Short
                (Input_Packet.Bytes (Query_End_Byte + 4))*256 +
              DNS_Types.Unsigned_Short
                (Input_Packet.Bytes (Query_End_Byte + 5));
            --EDNS_Rec.RCODE   := Input_Packet.Bytes(Query_End_Byte+6);
            --EDNS_Rec.Version := Input_Packet.Bytes(Query_End_Byte+7);
            EDNS_Rec.ZTop    := Input_Packet.Bytes (Query_End_Byte + 8);
            --EDNS_Rec.ZBottom := Input_Packet.Bytes(Query_End_Byte+9);
            --EDNS_Rec.RDLEN    := DNS_Types.Unsigned_Short(
            --  Input_Packet.Bytes(Query_End_Byte+10))*256+
            --  DNS_Types.Unsigned_Short
            --    (Input_Packet.Bytes(Query_End_Byte+11));

            -- when we respond, we'll respond with AT LEAST UDP_Max_Size,
            -- but no bigger than our Packet_Size
            Max_Transmit :=
              DNS_Types.Packet_Length_Range
                (DNS_Types.Unsigned_Short'Min (DNS_Types.Packet_Size,
                                               EDNS_Rec.Payload_Size));
            Max_Transmit :=
              DNS_Types.Packet_Length_Range'Max (DNS_Types.UDP_Max_Size,
                                                 Max_Transmit);

            Output_Packet.Bytes (Start_Byte + 1) := 0;
            -- high order byte of OPT is 0
            Output_Packet.Bytes (Start_Byte + 2) := 0;
            -- the mod here is superfluous as OPT = 41
            --# accept Warning, 12, From_Query_Type, "unchecked conversions ok";
            Output_Packet.Bytes (Start_Byte + 3) :=
              DNS_Types.Byte (From_Query_Type (DNS_Types.Opt) mod 256);

            -- split unsigned short into two bytes
            Output_Packet.Bytes (Start_Byte + 4) :=
              DNS_Types.Byte (Max_Transmit/256);
            Output_Packet.Bytes (Start_Byte + 5) :=
              DNS_Types.Byte(Max_Transmit mod 256);

            Output_Packet.Bytes (Start_Byte + 6) := 0;
            Output_Packet.Bytes (Start_Byte + 7) := 0;
            -- FLAGS (DNSSec only), see RFC 3225
            if (EDNS_Rec.ZTop and Dns_Types.DNSSecMask) /= 0 then
               Output_Packet.Bytes (Start_Byte + 8) := Dns_Types.DNSSecMask;
               DNSSec := True;
            else
               Output_Packet.Bytes (Start_Byte + 8) := 0;
            end if;
            Output_Packet.Bytes (Start_Byte + 9) := 0;
            -- RDLen = 0
            Output_Packet.Bytes (Start_Byte + 10) := 0;
            Output_Packet.Bytes (Start_Byte + 11) := 0;

            Additional_Count := Additional_Count + 1;
            Output_Bytes :=
              DNS_Types.Packet_Length_Range
                ((Start_Byte + 11) +
                 DNS_Types.Packet_Bytes_Range (DNS_Types.Header_Bits/8));
         end if;
      end if;
   end Create_Response_EDNS;

   procedure Create_Response
     (Input_Packet  : in     DNS_Types.DNS_Packet;
      Input_Bytes   : in     DNS_Types.Packet_Length_Range;
      Output_Packet : in out DNS_Types.DNS_Packet;
      Output_Bytes  :    out DNS_Types.Packet_Length_Range;
      Max_Transmit  :    out DNS_Types.Packet_Length_Range)
   is
      Start_Byte           : DNS_Types.Packet_Bytes_Range;
      Query_End_Byte       : DNS_Types.Packet_Bytes_Range;
      DomainName           : RR_Type.WireStringType;
      Query_Type           : DNS_Types.Query_Type;
      Query_Class          : DNS_Types.Query_Class;
      NumFound             : Natural;
      Counter              : Natural;
      QName_Location       : DNS_Types.QName_Ptr_Range := 12;
      QName_Locations      : QName_Ptr_Range_Array;
      ReturnedCNameRecords : RR_Type.CName_Record_Type.CNameRecordBucketType;
      NS_Replies           : RR_Type.NS_Record_Type.NSRecordBucketType;
      MX_Replies           : RR_Type.MX_Record_Type.MXRecordBucketType;
      Srv_Replies          : RR_Type.Srv_Record_Type.SrvRecordBucketType;
      Answer_Count         : DNS_Types.Unsigned_Short;
      Additional_Count     : DNS_Types.Unsigned_Short;
      DNSSec               : Boolean;
   begin

      Output_Packet.Header    := Input_Packet.Header;
      Output_Packet.Header.AA := False;
      Output_Packet.Header.QR := True;
      -- Keep # of queries and send the query back!! (i.e. don't do line below)
      -- Response_Header.QDCOUNT := 0;

      pragma Assert_And_Cut
        (Integer (Input_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
         QName_Location >= 0 and
         QName_Location < 16384 and
         Integer (Input_Bytes) < 312);

      Get_Query_Name_Type_Class
        (Input_Packet,
         Input_Bytes,
         DomainName,
         Query_Type,
         Query_Class,
         Query_End_Byte);
      Start_Byte := Query_End_Byte;
      --Start_Byte := DNS_Types.Packet_Bytes_Range(Input_Bytes) -
      --   DNS_Types.Packet_Bytes_Range(DNS_Types.Header_Bits/8);
      for I in DNS_Types.Packet_Bytes_Range range 1 .. Start_Byte loop
         pragma Loop_Invariant
           (Integer (Input_Bytes) >= DNS_Types.Header_Bits/8 and
            QName_Location >= 0 and
            QName_Location < 16384 and
            Integer (Input_Bytes) < 312 and
            Start_Byte <= DNS_Types.Packet_Bytes_Range (Input_Bytes) and
            Start_Byte >= 4);
         Output_Packet.Bytes (I) := Input_Packet.Bytes (I);
      end loop;

      -- we start out with no responses
      Output_Packet.Header.ANCount := 0;

      DNS_Table_Pkg.DNS_Table.QueryCNameRecords
        (DomainName      => DomainName,
         ReturnedRecords => ReturnedCNameRecords,
         HowMany         => NumFound);

      if NumFound > 1 then
         Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
           (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
            "more than one cname?",
            0);
      elsif NumFound = 1 then
         Process_Response_CName
           (Start_Byte     => Start_Byte,
            CNames         => ReturnedCNameRecords,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Output_Bytes   => Output_Bytes);

         Start_Byte :=
           DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                         DNS_Types.Header_Bits/8);
      end if;
      Answer_Count := Output_Packet.Header.ANCount;
      Additional_Count := 0;
      --ada.text_io.put_line("numfound: " & integer'image(numfound));
      if Query_Class /= DNS_Types.In_Class then
         Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
           (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
            "bad query class",
            0);
         -- Ada.Text_IO.Put_Line ("qc: " &
         --                       DNS_Types.Query_Class'Image (Query_Class));
         Create_Response_Error
           (Input_Bytes   => Input_Bytes,
            Output_Packet => Output_Packet,
            Output_Bytes  => Output_Bytes);
      elsif Query_Type = DNS_Types.Any then
         Create_Response_A
           (Start_Byte     => Start_Byte,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Answer_Count   => Answer_Count,
            Output_Bytes   => Output_Bytes);
         Start_Byte := DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                                     DNS_Types.Header_Bits/8);
         Create_Response_AAAA
           (Start_Byte     => Start_Byte,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Answer_Count   => Answer_Count,
            Output_Bytes   => Output_Bytes);
         Start_Byte := DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                                     DNS_Types.Header_Bits/8);

         Create_Response_MX
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            Num_Found       => NumFound,
            QName_Location  => QName_Location,
            QName_Locations => QName_Locations,
            Replies         => MX_Replies,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);

         Start_Byte := DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                                     DNS_Types.Header_Bits/8);

         Create_Response_NS
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            Num_Found       => NumFound,
            QName_Location  => QName_Location,
            QName_Locations => QName_Locations,
            Replies         => NS_Replies,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);

         Start_Byte := DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                                     DNS_Types.Header_Bits/8);

         Create_Response_Srv
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            Num_Found       => NumFound,
            QName_Location  => QName_Location,
            QName_Locations => QName_Locations,
            Replies         => Srv_Replies,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);

         Start_Byte := DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                                     DNS_Types.Header_Bits/8);
         Create_Response_Ptr
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            QName_Location  => QName_Location,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);

         Start_Byte := DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                                     DNS_Types.Header_Bits/8);
         Create_Response_SOA
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            QName_Location  => QName_Location,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes); --DNS_Types.Any
      elsif Query_Type = DNS_Types.SOA then
         Create_Response_SOA
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            QName_Location  => QName_Location,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);
      elsif Query_Type = DNS_Types.Ptr then
         Create_Response_Ptr
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            QName_Location  => QName_Location,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);
      elsif Query_Type = DNS_Types.A then
         Create_Response_A
           (Start_Byte     => Start_Byte,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Answer_Count   => Answer_Count,
            Output_Bytes   => Output_Bytes);
      elsif Query_Type = DNS_Types.AAAA then
         Create_Response_AAAA
           (Start_Byte     => Start_Byte,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Answer_Count   => Answer_Count,
            Output_Bytes   => Output_Bytes);
      elsif Query_Type = DNS_Types.DNSKey then   --BSF 24 Aug 2012
         Create_Response_DNSKey
           (Start_Byte     => Start_Byte,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Answer_Count   => Answer_Count,
            Output_Bytes   => Output_Bytes);
      elsif Query_Type = DNS_Types.NSec then   --BSF 2 Oct 2012
         Create_Response_NSec
           (Start_Byte     => Start_Byte,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Answer_Count   => Answer_Count,
            Output_Bytes   => Output_Bytes);
      elsif Query_Type = DNS_Types.RRSig then   --BSF 11 Sep 2012
         Create_Response_RRSig
           (Start_Byte     => Start_Byte,
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Answer_Count   => Answer_Count,
            Output_Bytes   => Output_Bytes);
      elsif Query_Type = DNS_Types.MX then
         Create_Response_MX
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            Num_Found       => NumFound,
            QName_Location  => QName_Location,
            QName_Locations => QName_Locations,
            Replies         => MX_Replies,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);
         Counter := 1;
         Additional_Count := 0;
         while Counter <= NumFound
           and Additional_Count < DNS_Types.Unsigned_Short'Last -
                                  DNS_Types.Unsigned_Short
                                    (2*Rr_Type.MaxNumRecords)
         loop

            pragma Loop_Invariant
              (Counter >= 1 and
               Counter <= NumFound and
               Answer_Count >= 0 and
               Answer_Count <= 65535 and
               Additional_Count >= 0 and
               (for all Z in RR_Type.ReturnedRecordsIndexType =>
                  QName_Locations (Z) >= 0 and
                  QName_Locations (Z) < 16384) and
               QName_Location >= 0 and
               QName_Location <= 16383 and
               Additional_Count < DNS_Types.Unsigned_Short'Last -
                                  DNS_Types.Unsigned_Short
                                    (2*RR_Type.MaxNumRecords) and
               NumFound >= 0 and
               NumFound <= RR_Type.MaxNumRecords and
               Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
               Integer(Output_Bytes) <= DNS_Types.Packet_Size);
            Start_Byte :=
              DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                            DNS_Types.Header_Bits/8);
            Create_Response_A
              (Start_Byte     => Start_Byte,
               DomainName     => MX_Replies (Counter).MailExchanger,
               Qname_Location => QName_Locations (Counter),
               Output_Packet  => Output_Packet,
               Answer_Count   => Additional_Count,
               Output_Bytes   => Output_Bytes);
            Start_Byte :=
              DNS_Types.Packet_Bytes_Range (Integer (Output_Bytes) -
                                            DNS_Types.Header_Bits/8);
            Create_Response_AAAA
              (Start_Byte     => Start_Byte,
               DomainName     => MX_Replies (Counter).MailExchanger,
               Qname_Location => Qname_Locations (Counter),
               Output_Packet  => Output_Packet,
               Answer_Count   => Additional_Count,
               Output_Bytes   => Output_Bytes);
            Counter := Counter + 1;
         end loop;
      elsif Query_Type = DNS_Types.Srv then
         Create_Response_Srv
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            Num_Found       => NumFound,
            QName_Location  => QName_Location,
            QName_Locations => QName_Locations,
            Replies         => Srv_Replies,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);
         Counter := 1;
         Additional_Count := 0;
         while Counter <= NumFound
           and Additional_Count < DNS_Types.Unsigned_Short'Last -
                                  DNS_Types.Unsigned_Short
                                    (2*Rr_Type.MaxNumRecords)
         loop
            pragma Loop_Invariant
              (Counter >= 1 and
               Counter <= NumFound and
               Answer_Count >= 0 and
               Answer_Count <= 65535 and
               Additional_Count >= 0 and
               (for all Z in RR_Type.ReturnedRecordsIndexType =>
                  QName_Locations (Z) >= 0 and
                  QName_Locations (Z) < 16384) and
               QName_Location >= 0 and
               QName_Location <= 16383 and
               Additional_Count < DNS_Types.Unsigned_Short'Last -
                                  DNS_Types.Unsigned_Short
                                    (2*RR_Type.MaxNumRecords) and
               NumFound >= 0 and
               NumFound <= RR_Type.MaxNumRecords and
               Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
               Integer(Output_Bytes) <= DNS_Types.Packet_Size);
            Start_Byte := DNS_Types.Packet_Bytes_Range
                            (Integer (Output_Bytes) -
                             DNS_Types.Header_Bits/8);
            Create_Response_A
              (Start_Byte     => Start_Byte,
               DomainName     => Srv_Replies (Counter).Servername,
               QName_Location => QName_Locations (Counter),
               Output_Packet  => Output_Packet,
               Answer_Count   => Additional_Count,
               Output_Bytes   => Output_Bytes);
            Start_Byte := DNS_Types.Packet_Bytes_Range
                            (Integer (Output_Bytes) -
                             DNS_Types.Header_Bits/8);
            Create_Response_AAAA
              (Start_Byte     => Start_Byte,
               DomainName     => Srv_Replies (Counter).Servername,
               QName_Location => QName_Locations (Counter),
               Output_Packet  => Output_Packet,
               Answer_Count   => Additional_Count,
               Output_Bytes   => Output_Bytes);
            Counter := Counter + 1;
         end loop;
      elsif Query_Type = DNS_Types.NS then
         Create_Response_NS
           (Start_Byte      => Start_Byte,
            DomainName      => DomainName,
            Num_Found       => NumFound,
            QName_Location  => QName_Location,
            QName_Locations => QName_Locations,
            Replies         => NS_Replies,
            Output_Packet   => Output_Packet,
            Answer_Count    => Answer_Count,
            Output_Bytes    => Output_Bytes);
         Counter := 1;
         Additional_Count := 0;
         while Counter <= NumFound
           and Additional_Count < DNS_Types.Unsigned_Short'Last -
                                  DNS_Types.Unsigned_Short
                                    (2*RR_Type.MaxNumRecords)
         loop
            pragma Loop_Invariant
              (Counter >= 1 and
               Counter <= NumFound and
               (for all Z in RR_Type.ReturnedRecordsIndexType =>
                  Qname_Locations(Z) >= 0 and
                  Qname_Locations(Z) < 16384) and
               QName_Location >= 0 and
               QName_Location <= 16383 and
               Answer_Count >=0 and
               Answer_Count <= 65535 and
               Additional_Count >= 0 and
               Additional_Count < DNS_Types.Unsigned_Short'Last -
                                  DNS_Types.Unsigned_Short
                                    (2*RR_Type.MaxNumRecords) and
               NumFound >= 0 and
               NumFound <= RR_Type.MaxNumRecords and
               Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
               Integer (Output_Bytes) <= DNS_Types.Packet_Size);
            Start_Byte := DNS_Types.Packet_Bytes_Range
                            (Integer (Output_Bytes) -
                             DNS_Types.Header_Bits/8);
            Create_Response_A
              (Start_Byte     => Start_Byte,
               DomainName     => NS_Replies (Counter).Nameserver,
               QName_Location => QName_Locations (Counter),
               Output_Packet  => Output_Packet,
               Answer_Count   => Additional_Count,
               Output_Bytes   => Output_Bytes);
            Start_Byte := DNS_Types.Packet_Bytes_Range
                            (Integer (Output_Bytes) -
                             DNS_Types.Header_Bits/8);
            Create_Response_AAAA
              (Start_Byte     => Start_Byte,
               DomainName     => NS_Replies (Counter).Nameserver,
               QName_Location => QName_Locations (Counter),
               Output_Packet  => Output_Packet,
               Answer_Count   => Additional_Count,
               Output_Bytes   => Output_Bytes);
            Counter := Counter + 1;
         end loop;
      else
         Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
           (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
            "bad query type",
            0);
         -- Ada.Text_IO.Put_Line ("qc: " &
         --                       DNS_Types.Query_Type'Image (Query_Type));
         Create_Response_Error
           (Input_Bytes   => Input_Bytes,
            Output_Packet => Output_Packet,
            Output_Bytes  => Output_Bytes);
      end if;

      -- this assert helps with the VCG Heap overflow
      pragma Assert_And_Cut
        (Answer_Count >= 0 and
         Answer_Count <= 65535 and
         QName_Location >= 0 and
         QName_Location < 16384 and
         Additional_Count >= 0 and
         NumFound >= 0 and
         NumFound <= RR_Type.MaxNumRecords and
         Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
         Integer (Output_Bytes) <= DNS_Types.Packet_Size);

      DNSSec := False;
      Max_Transmit := DNS_Types.UDP_Max_Size;
      -- Handle EDNS additional OPT record here!
      if Input_Packet.Header.QDCount = 1 and
         Input_Packet.Header.ARCount = 1 and
         Additional_Count < DNS_Types.Unsigned_Short'Last then
         Start_Byte := DNS_Types.Packet_Bytes_Range
                         (Integer (Output_Bytes) - DNS_Types.Header_Bits/8);
         Create_Response_EDNS
           (Input_Packet     => Input_Packet,
            Input_Bytes      => Input_Bytes,
            Query_End_Byte   => Query_End_Byte,
            Start_Byte       => Start_Byte,
            Output_Packet    => Output_Packet,
            Output_Bytes     => Output_Bytes,
            Additional_Count => Additional_Count,
            DNSSec           => DNSSec,
            Max_Transmit     => Max_Transmit);
      elsif Input_Packet.Header.QDCount /= 1 then
         Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
           (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
            "query count > 1",
            0);
      elsif Input_Packet.Header.ARCount > 1 then
         Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
           (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
            "ar count > 1",
            0);
      end if;

      -- this assert helps with the VCG Heap overflow
      pragma Assert_And_Cut
        (Answer_Count >= 0 and
         Answer_Count <= 65535 and
         QName_Location >= 0 and
         QName_Location < 16384 and
         Additional_Count >= 0 and
         NumFound >= 0 and
         NumFound <= RR_Type.MaxNumRecords and
         Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
         Integer (Max_Transmit) <= DNS_Types.Packet_Size and
         Max_Transmit >= DNS_Types.UDP_Max_Size and
         Integer (Output_Bytes) <= DNS_Types.Packet_Size);

      if DNSSec and Answer_Count > 0 then
         Output_Bytes := (Output_Bytes-1) + 1;
      end if;

      Output_Packet.Header.ANCount := Answer_Count;
      Output_Packet.Header.ARCount := Additional_Count;
      if Answer_Count > 0 then
         -- our answer is authoritative
         Output_Packet.Header.AA := True;
         Output_Packet.Header.RCode := DNS_Types.No_Error;
      elsif Output_Packet.Header.AA = False then
         Create_NXDomain_Response
           (Start_Byte     => DNS_Types.Packet_Bytes_Range (Input_Bytes) -
                              DNS_Types.Packet_Bytes_Range
                                (DNS_Types.Header_Bits/8),
            DomainName     => DomainName,
            QName_Location => QName_Location,
            Output_Packet  => Output_Packet,
            Output_Bytes   => Output_Bytes);
      end if;
   end Create_Response;

   procedure Process_Request_TCP (Reply_Socket : in DNS_Network.DNS_Socket) is
      Input_Packet  : DNS_Types.DNS_TCP_Packet;
      Input_Bytes   : DNS_Types.Packet_Length_Range;
      Output_Packet : DNS_Types.DNS_TCP_Packet;
      Output_Bytes  : DNS_Types.Packet_Length_Range;
      Max_Transmit  : DNS_Types.Packet_Length_Range;
      Failure       : Boolean;
   begin
      --Output_Packet.Rest.Bytes := DNS_Types.Bytes_Array_Type'(others => 0);

      DNS_Network_Receive.Receive_DNS_Packet_TCP
        (Packet       => Input_Packet,
         Number_Bytes => Input_Bytes,
         Socket       => Reply_Socket,
         Failure      => Failure);
      -- SPARK_IO_05.Put_Line (SPARK_IO_05.Standard_Output, "Input ID", 0);
      -- SPARK_IO_05.Put_Integer (SPARK_IO_05.Standard_Output,
      --                          Integer (Input_Packet.Rest.Header.MessageID),
      --                          0,
      --                          16);
      -- SPARK_IO_05.New_Line (SPARK_IO_05.Standard_Output, 1);
      if Failure then
         -- Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
         --   (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
         --    "Receive failed",
         --    0);
         null;
      else
         -- Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
         --   (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
         --    "got packet",
         --    0);
         Create_Response
           (Input_Packet  => Input_Packet.Rest,
            Input_Bytes   => Input_Bytes,
            Output_Packet => Output_Packet.Rest,
            Output_Bytes  => Output_Bytes,
            Max_Transmit  => Max_Transmit);
         -- Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
         --   (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
         --    "Reply created",
         --    0);
         if System.Default_Bit_Order=System.Low_Order_First then
            Output_Packet.Length :=
              DNS_Types.Byte_Swap_US (DNS_Types.Unsigned_Short (Output_Bytes));
         else
            Output_Packet.Length := DNS_Types.Unsigned_Short (Output_Bytes);
         end if;
         -- SPARK_IO_05.Put_Line (SPARK_IO_05.Standard_Output,"Output ID", 0);
         -- SPARK_IO_05.Put_Integer
         --   (SPARK_IO_05.Standard_Output,
         --    Integer (Output_Packet.Rest.Header.MessageID),
         --    0,
         --    16);
         -- SPARK_IO_05.New_Line (SPARK_IO_05.Standard_Output, 1);
         -- Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
         --   (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
         --    "sending",
         --    0);

         DNS_Network.Send_DNS_Packet_TCP
           (Packet       => Output_Packet,
            Number_Bytes => Output_Bytes,
            Socket       => Reply_Socket,
            Failure      => Failure);
         if Failure then
            Protected_SPARK_IO_05.SPARK_IO_PO.Put_Integer
              (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
               Integer (Output_Packet.Rest.Header.MessageID),
               0,
               16);
            Protected_SPARK_IO_05.SPARK_IO_PO.Put_Line
              (Protected_SPARK_IO_05.SPARK_IO_PO.Standard_Output,
               "Respond failed",
               0);
         end if;
      end if;
   end Process_Request_TCP;

end Process_DNS_Request;
