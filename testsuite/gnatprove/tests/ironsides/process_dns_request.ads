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

with DNS_Types,
     DNS_Network,
     DNS_Network_Receive,
     DNS_Table_Pkg,
     Protected_SPARK_IO_05,
     RR_Type,
     RR_Type.A_Record_Type,
     RR_Type.AAAA_Record_Type,
     RR_Type.CName_Record_Type,
     RR_Type.DNSKey_Record_Type,
     RR_Type.NS_Record_Type,
     RR_Type.NSec_Record_Type,
     RR_Type.MX_Record_Type,
     RR_Type.RRSig_Record_Type,
     RR_Type.Srv_Record_Type,
     RR_Type.Ptr_Record_Type,
     RR_Type.SOA_Record_Type,
     Unsigned_Types;

use type DNS_Types.Packet_Bytes_Range,
         DNS_Types.Packet_Length_Range,
         DNS_Types.QName_Ptr_Range,
         DNS_Types.Unsigned_Short;

package Process_DNS_Request is
   procedure Process_Request_TCP (Reply_Socket : in DNS_Network.DNS_Socket)
   with Global  => (In_Out => (DNS_Table_Pkg.DNS_Table,
                               DNS_Network.Network,
                               Protected_SPARK_IO_05.SPARK_IO_PO)),
        Depends => ((DNS_Network.Network,
                     Protected_SPARK_IO_05.SPARK_IO_PO) =>+
                      (DNS_Network.Network,
                       DNS_Table_Pkg.DNS_Table,
                       Reply_Socket),
                    DNS_Table_Pkg.DNS_Table =>+ null);

   procedure Create_Response
     (Input_Packet  : in     DNS_Types.DNS_Packet;
      Input_Bytes   : in     DNS_Types.Packet_Length_Range;
      Output_Packet : in out DNS_Types.DNS_Packet;
      Output_Bytes  :    out DNS_Types.Packet_Length_Range;
      Max_Transmit  :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => (DNS_Table_Pkg.DNS_Table,
                               Protected_SPARK_IO_05.SPARK_IO_PO)),
        Depends => (Max_Transmit => (DNS_Table_Pkg.DNS_Table,
                                     Input_Bytes,
                                     Input_Packet),
                    (Output_Bytes,
                     Output_Packet) => (DNS_Table_Pkg.DNS_Table,
                                        Input_Bytes,
                                        Input_Packet,
                                        Output_Packet),
                    Protected_SPARK_IO_05.SPARK_IO_PO =>+
                      (DNS_Table_Pkg.DNS_Table,
                       Input_Bytes,
                       Input_Packet),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer (Input_Bytes) >= DNS_Types.Header_Bits / 8 + 1 and
                   Integer (Input_Bytes) < 312,
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits / 8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Integer (Max_Transmit) <= DNS_Types.Packet_Size and
                   Max_Transmit >= DNS_Types.UDP_Max_Size;
private
   procedure Set_Unsigned_32
     (Bytes      : in out DNS_Types.Bytes_Array_Type;
      Start_Byte : in     DNS_Types.Packet_Bytes_Range;
      Value      : in     Unsigned_Types.Unsigned32)
   with Depends => (Bytes =>+ (Start_Byte, Value)),
        Pre     => Start_Byte <= DNS_Types.Packet_Bytes_Range'Last-3;

   procedure Set_Unsigned_16
     (Bytes      : in out DNS_Types.Bytes_Array_Type;
      Start_Byte : in     DNS_Types.Packet_Bytes_Range;
      Value      : in     Unsigned_Types.Unsigned16)
   with Depends => (Bytes =>+ (Start_Byte, Value)),
        Pre     => Start_Byte <= DNS_Types.Packet_Bytes_Range'Last-1;

   procedure Get_Query_Name_Type_Class
     (Input_Packet  : in     DNS_Types.DNS_Packet;
      Input_Bytes   : in     DNS_Types.Packet_Length_Range;
      DomainName    :    out RR_Type.WireStringType;
      Query_Type    :    out DNS_Types.Query_Type;
      Query_Class   :    out DNS_Types.Query_Class;
      End_Byte      :    out Dns_types.Packet_Bytes_Range)
   with Depends => ((DomainName,
                     End_Byte,
                     Query_Class,
                     Query_Type) => (Input_Bytes, Input_Packet)),
        Pre     => Input_Bytes >=DNS_Types.Header_Bits/8 + 1 and
                   Input_Bytes < 1000,
        Post    => Integer (End_Byte) <= Integer (Input_Bytes) and
                   End_Byte >= 4;

   procedure Set_TTL_Data_IP
     (Bytes      : in out DNS_Types.Bytes_Array_Type;
      Start_Byte : in DNS_Types.Packet_Bytes_Range;
      A_Record   : in Rr_Type.A_Record_Type.ARecordType)
   with Depends => (Bytes =>+ (A_Record, Start_Byte)),
        Pre     => Start_Byte <= DNS_Types.Packet_Bytes_Range'Last-10;

   procedure Set_TTL_Data_DNSKEY--BSF
     (Bytes         : in out DNS_Types.Bytes_Array_Type;
      Start_Byte    : in     DNS_Types.Packet_Bytes_Range;
      DNSKey_Record : in     RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      DstBytes      :    out RR_Type.DNSKey_Record_Type.KeyLengthValueType)
   with Depends => (Bytes =>+ (DNSKey_Record, Start_Byte),
                    DstBytes => DNSKey_Record),
        Pre     => Start_Byte <= DNS_Types.Packet_Bytes_Range'Last - 10 -
                                 DNS_Types.Packet_Bytes_Range
                                   (DNSKey_Record.KeyLength);

   procedure Set_TTL_Data_NSec--BSF
     (Bytes       : in out DNS_Types.Bytes_Array_Type;
      Start_Byte  : in DNS_Types.Packet_Bytes_Range;
      NSec_Record : in Rr_Type.NSEC_Record_Type.NSecRecordType;
      DstBytes    : out DNS_Types.Packet_Length_Range)
   with Depends => (Bytes =>+ (NSec_Record, Start_Byte),
                    DstBytes => NSec_Record),
        Pre     => Start_Byte <= DNS_Types.Packet_Bytes_Range'Last - 6 -
                                 DNS_Types.Packet_Bytes_Range
                                   (RR_Type.MaxDomainNameLength + 1) -
                                 DNS_Types.Packet_Bytes_Range
                                   (RR_Type.NSec_Record_Type.MaxRRDataLength),
        Post    => DstBytes <= DNS_Types.Packet_Length_Range
                                 (RR_Type.NSec_Record_Type.MaxRRDataLength);

   procedure Set_TTL_Data_RRSig--BSF
     (Bytes        : in out DNS_Types.Bytes_Array_Type;
      Start_Byte   : in     DNS_Types.Packet_Bytes_Range;
      RRSig_Record : in     RR_Type.RRSig_Record_Type.RRSigRecordType;
      DstBytes     :    out DNS_Types.Packet_Bytes_Range)
   with Depends => (Bytes =>+ (RRSig_Record, Start_Byte),
                    DstBytes => RRSig_Record),
        Pre     => Start_Byte <= DNS_Types.Packet_Bytes_Range'Last - 24 -
                                 DNS_Types.Packet_Bytes_Range
                                   (RR_Type.MaxDomainNameLength) -
                                 DNS_Types.Packet_Bytes_Range
                                   (RR_Type.RRSig_Record_Type.MaxRRSigLength),
        Post    => DstBytes <= DNS_Types.Packet_Bytes_Range
                                 (24 + RR_Type.MaxDomainNameLength +
                                  RR_Type.RRSig_Record_Type.MaxRRSigLength);

   procedure Set_TTL_Data_AAAA_IP
     (Bytes       : in out DNS_Types.Bytes_Array_Type;
      Start_Byte  : in     DNS_Types.Packet_Bytes_Range;
      AAAA_Record : in     RR_Type.AAAA_Record_Type.AAAARecordType)
   with Depends => (Bytes =>+ (AAAA_Record, Start_Byte)),
        Pre     => Start_Byte <= DNS_Types.Packet_Bytes_Range'Last-22;

   procedure Set_TTL_Data_NS_Response
     (Bytes               : in out DNS_Types.Bytes_Array_Type;
      Start_Byte          : in     DNS_Types.Packet_Bytes_Range;
      NS_Record           : in     RR_Type.NS_Record_Type.NSRecordType;
      Current_Name_Length : in     RR_Type.WireStringTypeIndex)
   with Depends => (Bytes =>+ (Current_Name_Length, NS_Record, Start_Byte)),
        Pre     => Current_Name_Length >= 0 and
                   Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
                   Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 6) -
                                 DNS_Types.Packet_Bytes_Range
                                   (Current_Name_Length);

   procedure Set_TTL_Data_Ptr_Response
     (Bytes                : in out DNS_Types.Bytes_Array_Type;
      Start_Byte           : in     DNS_Types.Packet_Bytes_Range;
      Ptr_Record           : in     RR_Type.Ptr_Record_Type.PtrRecordType;
      Current_Name_Length  : in     RR_Type.WireStringTypeIndex)
   with Depends => (Bytes =>+ (Current_Name_Length, PTR_Record, Start_Byte)),
        Pre     => Current_Name_Length >= 0 and
                   Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
                   Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last -6 ) -
                                 DNS_Types.Packet_Bytes_Range
                                   (Current_Name_Length);

   procedure Set_TTL_Data_MX_Response
     (Bytes               : in out DNS_Types.Bytes_Array_Type;
      Start_Byte          : in     DNS_Types.Packet_Bytes_Range;
      MX_Record           : in     RR_Type.MX_Record_Type.MXRecordType;
      Current_Name_Length : in     RR_Type.WireStringTypeIndex)
   with Depends => (Bytes =>+ (Current_Name_Length, MX_Record, Start_Byte)),
        Pre     => Current_Name_Length >= 0 and
                   Current_Name_Length <= RR_Type.WireStringTypeIndex'Last and
                   Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 8) -
                                 DNS_Types.Packet_Bytes_Range
                                   (Current_Name_Length);

   procedure Set_TTL_Data_SOA_Response
     (Bytes                  : in out DNS_Types.Bytes_Array_Type;
      Start_Byte             : in     DNS_Types.Packet_Bytes_Range;
      SOA_Record             : in     RR_Type.SOA_record_type.SOARecordType;
      Nameserver_Name_Length : in     RR_Type.WireStringTypeIndex;
      Mailbox_Name_Length    : in     RR_Type.WireStringTypeIndex)
   with Depends => (Bytes =>+ (Mailbox_Name_Length,
                               Nameserver_Name_Length,
                               SOA_Record,
                               Start_Byte)),
        Pre     =>
          Nameserver_Name_Length >= 0 and
          Nameserver_Name_Length <= RR_Type.WireStringTypeIndex'Last and
          Mailbox_Name_Length >= 0 and
          Mailbox_Name_Length <= RR_Type.WireStringTypeIndex'Last and
          Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 26) -
                        DNS_Types.Packet_Bytes_Range
                          (Nameserver_Name_Length+Mailbox_Name_Length);


   procedure Set_TTL_Data_SRV_Response
     (Bytes               : in out DNS_Types.Bytes_Array_Type;
      Start_Byte          : in     DNS_Types.Packet_Bytes_Range;
      Srv_Record          : in     RR_Type.Srv_record_type.SrvRecordType;
      Current_Name_Length : in     RR_Type.WireStringTypeIndex)
   with Depends => (Bytes =>+ (Current_Name_Length, SRV_Record, Start_Byte)),
        Pre     => Current_Name_Length >= 0 and
                   Current_Name_Length<=RR_Type.WireStringTypeIndex'Last and
                   Start_Byte <= (DNS_Types.Packet_Bytes_Range'Last - 12) -
                                 DNS_Types.Packet_Bytes_Range
                                   (Current_Name_Length);

   procedure Create_Response_EDNS
     (Input_Packet       : in     DNS_Types.DNS_Packet;
      Input_Bytes        : in     DNS_Types.Packet_Length_Range;
      Query_End_Byte     : in     DNS_Types.Packet_Bytes_Range;
      Start_Byte         : in     DNS_Types.Packet_Bytes_Range;
      Output_Packet      : in out DNS_Types.DNS_Packet;
      Output_Bytes       :    out DNS_Types.Packet_Length_Range;
      Additional_Count   : in out DNS_Types.Unsigned_Short;
      DNSSec             :    out Boolean;
      Max_Transmit       :    out DNS_Types.Packet_Length_Range)
   with Depends => ((Additional_Count,
                     Output_Packet) =>+ (Input_Bytes,
                                         Input_Packet,
                                         Query_End_Byte,
                                         Start_Byte),
                    (DNSSEC,
                     Max_Transmit,
                     Output_Bytes) => (Input_Bytes,
                                       Input_Packet,
                                       Query_End_Byte,
                                       Start_Byte)),
        Pre     => Additional_Count < DNS_Types.Unsigned_Short'Last,
        Post    => Integer(Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Output_Bytes <= DNS_Types.Packet_Size and
                   Additional_Count >= Additional_Count'Old and
                   Additional_Count <= Additional_Count'Old + 1 and
                   Max_Transmit >= DNS_Types.UDP_Max_Size and
                   Max_Transmit <= DNS_Types.Packet_Size;

   procedure Create_Response_A
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table,
                                      DomainName),
                    Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                    DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_types.Unsigned_Short
                                     (RR_Type.MaxNumRecords) and
                   Integer (Start_Byte) <= DNS_Types.Packet_Size,
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old +
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords);

   procedure Create_Response_DNSKey
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table,
                                      DomainName),
                    Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_types.Unsigned_Short
                                     (RR_Type.MaxNumRecords) and
                   Integer (Start_Byte) <= DNS_Types.Packet_Size,
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old +
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords);

   procedure Create_Response_NSec
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      QName_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table,
                                      DomainName),
                    Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_types.Unsigned_Short
                                     (RR_Type.MaxNumRecords),
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old +
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords);

   procedure Create_Response_RRSig
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QName_Ptr_Range;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out  => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table,
                                      DomainName),
                    Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_types.Unsigned_Short
                                     (RR_Type.MaxNumRecords) and
                   Integer (Start_Byte) <= DNS_Types.Packet_Size,
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old +
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords);

   procedure Create_NXDomain_Response
     (Start_Byte      : in     DNS_Types.Packet_Bytes_Range;
      DomainName      : in     RR_Type.WireStringType;
      Qname_Location  : in     DNS_Types.QName_Ptr_Range;
      Output_Packet   : in out DNS_Types.DNS_Packet;
      Output_Bytes    :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out  => DNS_Table_Pkg.DNS_Table),
        Depends => (Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     QName_Location,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer (Start_Byte) <= DNS_Types.Packet_Size,
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size;


   procedure Create_Response_AAAA
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QNAME_PTR_RANGE;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table, DomainName),
                    Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer (Start_Byte) <= DNS_Types.Packet_Size and
                   Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords),
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old +
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords);


   procedure Process_Response_CName
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      CNames         : in     RR_Type.cname_record_type.CNAMERecordBucketType;
      DomainName     :    out RR_Type.WireStringType;
      QName_Location : in out DNS_Types.QNAME_PTR_RANGE;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   with Depends => (DomainName => CNames,
                    Output_Bytes => (CNames,
                                     Start_Byte),
                    Output_Packet =>+ (CNames,
                                       QName_Location,
                                       Start_Byte),
                    QName_Location => Start_Byte),
        Pre     => Integer (Start_Byte) <= DNS_Types.Packet_Size and
                   Output_Packet.Header.ANCount = 0,
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Output_Packet.Header.ANCount <= 1;

   procedure Create_Response_Error
     (Input_Bytes   : in     DNS_Types.Packet_Length_Range;
      Output_Packet : in out DNS_Types.DNS_Packet;
      Output_Bytes  :    out DNS_Types.Packet_Length_Range)
   with Depends => (Output_Bytes => Input_Bytes,
                    Output_Packet =>+ null),
        Post    => Output_Bytes = Input_Bytes;

   type QName_Ptr_Range_Array is array (RR_Type.ReturnedRecordsIndexType)
     of DNS_Types.QName_Ptr_Range;

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
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table, DomainName),
                    (Num_Found,
                     Replies) => (DNS_Table_Pkg.DNS_Table,
                                  DomainName),
                    (Output_Bytes,
                     QName_Locations) => (DNS_Table_Pkg.DNS_Table,
                                          DomainName,
                                          Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer (Start_Byte) <= DNS_Types.Packet_Size and
                   Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_types.Unsigned_Short
                                     (RR_Type.MaxNumRecords),
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old + DNS_Types.Unsigned_Short
                                                        (RR_Type.MaxNumRecords);

   procedure Create_Response_Ptr
     (Start_Byte     : in     DNS_Types.Packet_Bytes_Range;
      DomainName     : in     RR_Type.WireStringType;
      Qname_Location : in     DNS_Types.QNAME_PTR_RANGE;
      Output_Packet  : in out DNS_Types.DNS_Packet;
      Answer_Count   : in out DNS_Types.Unsigned_Short;
      Output_Bytes   :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table, DomainName),
                    Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer(Start_Byte) <= DNS_Types.Packet_Size and
                   Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords),
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer(Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old + DNS_Types.Unsigned_Short
                                                        (RR_Type.MaxNumRecords);

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
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table, DomainName),
                    (Num_Found, Replies) => (DNS_Table_Pkg.DNS_Table,
                                             DomainName),
                    (Output_Bytes,
                     QName_Locations) => (DNS_Table_Pkg.DNS_Table,
                                          DomainName,
                                          Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer (Start_Byte) <= DNS_Types.Packet_Size and
                   Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords),
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old +
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords);

   procedure Create_Response_Srv
     (Start_Byte      : in     DNS_Types.Packet_Bytes_Range;
      DomainName      : in     RR_Type.WireStringType;
      Num_Found       :    out RR_Type.NumberOfRecordsType;
      Qname_Location  : in     DNS_Types.QName_Ptr_Range;
      Qname_Locations :    out QName_Ptr_Range_Array;
      Replies         :    out RR_Type.Srv_Record_Type.SrvRecordBucketType;
      Output_Packet   : in out DNS_Types.DNS_Packet;
      Answer_Count    : in out DNS_Types.Unsigned_Short;
      Output_Bytes    :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table, DomainName),
                    (Num_Found,
                     Replies) => (DNS_Table_Pkg.DNS_Table,
                                  DomainName),
                    (Output_Bytes,
                     Qname_Locations) => (DNS_Table_Pkg.DNS_Table,
                                          DomainName,
                                          Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer (Start_Byte) <= DNS_Types.Packet_Size and
                   Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords),
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old + DNS_Types.Unsigned_Short
                                                        (RR_Type.MaxNumRecords);

   procedure Create_Response_SOA
     (Start_Byte      : in     DNS_Types.Packet_Bytes_Range;
      DomainName      : in     RR_Type.WireStringType;
      QName_Location  : in     DNS_Types.QName_Ptr_Range;
      Output_Packet   : in out DNS_Types.DNS_Packet;
      Answer_Count    : in out DNS_Types.Unsigned_Short;
      Output_Bytes    :    out DNS_Types.Packet_Length_Range)
   with Global  => (In_Out => DNS_Table_Pkg.DNS_Table),
        Depends => (Answer_Count =>+ (DNS_Table_Pkg.DNS_Table, DomainName),
                    Output_Bytes => (DNS_Table_Pkg.DNS_Table,
                                     DomainName,
                                     Start_Byte),
                    Output_Packet =>+ (DNS_Table_Pkg.DNS_Table,
                                       DomainName,
                                       QName_Location,
                                       Start_Byte),
                   DNS_Table_Pkg.DNS_Table =>+ null),
        Pre     => Integer (Start_Byte) <= DNS_Types.Packet_Size and
                   Answer_Count <= DNS_Types.Unsigned_Short'Last -
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords),
        Post    => Integer (Output_Bytes) >= DNS_Types.Header_Bits/8 + 1 and
                   Integer (Output_Bytes) <= DNS_Types.Packet_Size and
                   Answer_Count <= Answer_Count'Old +
                                   DNS_Types.Unsigned_Short
                                     (RR_Type.MaxNumRecords);

   procedure Trim_Name
     (DomainName         : in     RR_Type.WireStringType;
      Trimmed_name       :    out RR_Type.WireStringType;
      QName_Location     : in     DNS_Types.QName_Ptr_Range;
      New_QName_Location :    out DNS_Types.QName_Ptr_Range)
   with Depends => (New_QName_Location => (DomainName, QName_Location),
                    Trimmed_Name => DomainName),
        Pre     => QName_Location <= DNS_Types.QName_Ptr_Range
                                       (DNS_Types.Packet_Length_Range'Last);
end Process_DNS_Request;
