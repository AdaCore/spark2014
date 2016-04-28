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

WITH Zone_File_IO,
     DNS_Table_Pkg,
     RR_Type.A_Record_Type,
     RR_Type.AAAA_Record_Type,
     RR_Type.CName_Record_Type,
     RR_Type.DNSKey_Record_Type,
     RR_Type.MX_Record_Type,
     RR_Type.NS_Record_Type,
     RR_Type.NSec_Record_Type,
     RR_Type.Ptr_Record_Type,
     RR_Type.RRSig_Record_Type,
     RR_Type.SOA_Record_Type,
     RR_Type.Srv_record_type,
     Unsigned_Types;

with Ada.Text_IO,
     SPARK.Text_IO;

procedure Driver is
   pragma Priority(0);
   ReturnedARecords      : RR_Type.A_Record_Type.ARecordBucketType;
   ReturnedAAAARecords   : RR_Type.AAAA_Record_Type.AAAARecordBucketType;
   ReturnedCNameRecords  : RR_Type.CName_Record_Type.CNameRecordBucketType;
   ReturnedDNSKeyRecords : RR_Type.DNSKey_Record_Type.DNSKeyRecordBucketType;
   ReturnedMXRecords     : RR_Type.MX_Record_Type.MXRecordBucketType;
   ReturnedSrvRecords    : Rr_Type.Srv_record_type.SrvRecordBucketType;
   ReturnedNSRecords     : RR_Type.NS_Record_Type.NSRecordBucketType;
   ReturnedNSecRecords   : RR_Type.NSec_Record_Type.NSecRecordBucketType;
   ReturnedPtrRecords    : RR_Type.Ptr_Record_Type.PtrRecordBucketType;
   ReturnedRRSigRecords  : RR_Type.RRSig_Record_Type.RRSigRecordBucketType;
   ReturnedSOARecords    : RR_Type.SOA_Record_Type.SOARecordBucketType;
   NumFound : Natural;
   --ZoneFileName : constant String := "tmp.zonefile";
   ZoneFileName          : constant String := "dfcs.usafa.edu.zonefile";
   --ZoneFileName : constant String := "db.dfcs.usafa.edu.signed";
   --ZoneFileName : constant String := "DFAN/usafa.hpc.mil.zonefile";
   --ZoneFileName : constant String := "DFAN/wedge.hpc.mil.zonefile";
   --ZoneFileName : constant String := "DFAN/wedge.iita.zonefile";
   --ZoneFileName : constant String := "DFAN/usafa.aero.zonefile";
   --ZoneFileName : constant String := "DFAN/research.usafa.edu.zonefile";
   --ZoneFileName : constant String := "DFAN/msrc.usafa.hpc.mil.zonefile";
   --ZoneFileName : constant String := "DFAN/edu.usafa.hpc.mil.zonefile";
   --ZoneFileName : constant String := "DFAN/10.in-addr.arpa.zonefile";
   --ZoneFileName : constant String := "DFAN/130.32.140.in-addr.arpa.zonefile";
   --ZoneFileName : constant String := "DFAN/castle.zonefile";
   --ZoneFileName : constant String := "DFAN/alabnet.zonefile";
   --zoneFileName : constant String := "DFAN/ipv6.usafa.edu.zonefile";
   --zoneFileName : constant String := "DFAN/alabnet.zonefile";

   function OpenZoneFile (FileName : in String) return boolean is
      ZoneFile : SPARK.Text_IO.File_Type;
      Success  : Boolean := True;
   begin
      SPARK.Text_IO.Open
        (The_File => ZoneFile,
         The_Mode => SPARK.Text_IO.In_File,
         The_Name => FileName,
         The_Form => "");

      if not SPARK.Text_IO.Is_Readable (ZoneFile) then
         Ada.Text_IO.Put ("Unable to open zone file " & ZoneFileName);
         Ada.Text_IO.New_Line;
         Ada.Text_IO.Put ("Check spelling, path, permissions etc and retry.");
         Ada.Text_IO.New_Line;
         return False;
      else
         Zone_File_IO.ProcesszoneFile (ZoneFile, Success);
         return Success;
      end if;
   end OpenZoneFile;

begin
   if OpenZoneFile (ZoneFileName) then
      DNS_Table_Pkg.DNS_Table.QueryARecords
        (RR_Type.ConvertStringToWire ("boleng.dfcs.usafa.edu."),
         ReturnedARecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image(NumFound) & " A records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("A record found, ipv4 = ");
         Ada.Text_IO.Put (Unsigned_Types.Unsigned32'Image
                            (ReturnedARecords (I).IPV4));
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryAAAARecords
        (RR_Type.ConvertStringToWire ("iPV6.dfcs.usafa.EDu."),
         ReturnedAAAARecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                            " AAAA records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("AAAA record found, ipv6(1) = ");
         Ada.Text_IO.Put (Unsigned_Types.Unsigned16'Image
                            (ReturnedAAAARecords (I).IPV6 (1)));
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryCNameRecords
        (RR_Type.ConvertStringToWire ("DOc.dfcs.usafa.edu."),
         ReturnedCNameRecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                             " CNAME records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("CNAME record found, canonical domain name = ");
         Ada.Text_IO.Put (ReturnedCNameRecords (I).CanonicalDomainName);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryDNSKeyRecords
        (RR_Type.ConvertStringToWire ("dfcs.usafa.edu."),
         ReturnedDNSKeyRecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                            " DNSKEY records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("DNSKEY record found, key = ");
         Ada.Text_IO.Put (ReturnedDNSKeyRecords (I).Key);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryMXRecords
        (RR_Type.ConvertStringToWire ("gibson.dfcs.USAFA.edu."),
         ReturnedMXRecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                            " MX records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("MX record found, pref/mailExchanger = ");
         Ada.text_io.Put (Unsigned_Types.Unsigned16'Image
                            (ReturnedMXRecords (I).Pref));
         Ada.Text_IO.Put ("   ");
         Ada.Text_IO.Put (ReturnedMXRecords (I).MailExchanger);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QuerySrvRecords
        (RR_Type.ConvertStringToWire ("_minecraft._tcp_gibson.dfcs.usafa.edu."),
         ReturnedSRVRecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image(NumFound) &
                            " SRV records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("SRV record found, pref/weight/portnum/servername= ");
         Ada.text_io.Put
           (Unsigned_Types.Unsigned16'Image (ReturnedSrvRecords (I).Pref));
         Ada.Text_IO.Put ("   ");
         Ada.text_io.Put (Unsigned_Types.Unsigned16'Image
                            (ReturnedSrvRecords (I).Weight));
         Ada.Text_IO.Put ("   ");
         Ada.text_io.Put
           (Unsigned_Types.Unsigned16'Image (ReturnedSrvRecords (I).Portnum));
         Ada.Text_IO.Put ("   ");
         Ada.Text_IO.Put (ReturnedSrvRecords (I).ServerName);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryNSecRecords
        (RR_Type.ConvertStringToWire ("dfcs.usafa.edu."),
         ReturnedNSecRecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                            " NSEC records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("NSEC record found, resource string = ");
         Ada.Text_IO.Put (ReturnedNSecRecords (I).RecordList);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryNSRecords
        (RR_type.ConvertStringToWire ("dfcS.Usafa.edu."),
         ReturnedNSRecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) & " NS records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("NS record found, nameserver = ");
         Ada.Text_IO.Put (ReturnedNSRecords (I).Nameserver);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryPtrRecords
        (RR_Type.ConvertStringToWire ("15.9.236.128.IN-addr.arpa."),
         ReturnedPtrRecords,
         NumFound);
      --Dns_Table_Pkg.DNS_Table.QueryPTRRecords
      --  (RR_Type.ConvertStringToWire("1.0.0.0.0.0.0.0.0.0.0.0.0.0.0.0.1.0.0.0.0.0.0.0.8.b.d.0.1.0.0.2.IP6.ARPA."),
      --   ReturnedPtrRecords,
      --   NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                            " PTR records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("PTR record found, domain name = ");
         Ada.Text_IO.Put (ReturnedPtrRecords (I).Domainname);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QueryRRSIGRecords
        (RR_Type.ConvertStringToWire ("dfcs.usafa.edu."),
         ReturnedRRSigRecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                            " RRSIG records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("RRSIG record found, signature = ");
         Ada.Text_IO.Put (ReturnedRRSigRecords (I).Signature);
         Ada.Text_IO.New_Line;
      end loop;

      DNS_Table_Pkg.DNS_Table.QuerySOARecords
        (RR_Type.ConvertStringToWire ("DFCS.usafa.EDU."),
         ReturnedSOARecords,
         NumFound);
      Ada.Text_IO.Put_Line (Integer'Image (NumFound) &
                            " SOA records returned");
      for I in Integer range 1 .. NumFound loop
         Ada.Text_IO.Put ("SOA record found, nameserver = ");
         Ada.Text_IO.Put (ReturnedSOARecords (I).Nameserver);
         Ada.Text_IO.New_Line;
      end loop;
   end if;
end Driver;
