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

with Non_Spark_Stuff,
     Error_Msgs,
     Ada.Characters.Handling,
     Ada.Characters.Latin_1,
     RR_Type.A_Record_Type,
     RR_Type.SOA_Record_Type;

use type RR_Type.RRItemType;

-- For Debugging purposes
with Ada.Text_IO;

package body Parser_Utilities is

   Blank        : constant Character := ' ';
   Tab          : constant Character := Ada.Characters.Latin_1.HT;
   Comment_Char : constant Character := ';';
   Control_Char : constant Character := '$';
   Origin_Char  : constant Character := '@';  --also definied in rr_type.adb
   L_Paren      : constant Character := '(';
   R_Paren      : constant Character := ')';

   SecondsInAMinute : constant natural := 60;
   MinutesInAnHour  : constant natural  := 60;
   HoursInADay      : constant natural  := 24;
   DaysInAWeek      : constant Natural  := 7;
   MaxDaysInAMonth  : constant Natural := 31;
   MonthsInAYear    : constant natural  := 12;

   --CH, CS, HS and IN are only valid namespace classes
   function IsClass
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      endIdx : in RR_Type.LineLengthIndex)
      return Boolean
   is
      Retval : Boolean;
      subtype Two_Range is Integer range 1 .. 2;
      subtype String2 is String (Two_Range);
      Class : String2 := "  ";
   begin
      --helps prover
      if BegIdx = EndIdx - 1 then
         Class (1) := Ada.Characters.Handling.To_Upper(S(BegIdx));
         Class (2) := Ada.Characters.Handling.To_Upper(S(endIdx));
         Retval    := (Class="CH") or else
                      (Class="CS") or else
                      (Class="HS") or else
                      (Class="IN");
      else
         Retval := False;
      end if;
      return Retval;
   end IsClass;

   --For now, only {A, AAAA, CName, DNSKey, MX, Srv, NS, Ptr, SOA}
   --records recognized
   --{RP, TXT recognized but not implemented}
   function IsRecord
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      EndIdx : in RR_Type.LineLengthIndex)
      return Boolean
     with Pre => BegIdx <= EndIdx
   is
      FirstChar   : Character;
      LastChar    : Character;
      LengthToken : RR_Type.LineLengthIndex;
      Retval      : Boolean;
   begin
      FirstChar:= Ada.Characters.Handling.To_Upper (S (BegIdx));
      LastChar := Ada.Characters.Handling.To_Upper (S (EndIdx));
      LengthToken := (EndIdx - BegIdx) + 1;
      --ugly but it gets the job done
      --A
      if FirstChar = 'A' and LengthToken = 1 then
         Retval := True;
      --NS
      elsif FirstChar = 'N' and LastChar = 'S' and LengthToken = 2 then
         Retval := True;
      --MX
      elsif FirstChar = 'M' and LastChar = 'X' and LengthToken = 2 then
         Retval := True;
      --RP
      elsif FirstChar = 'R' and LastChar = 'P' and LengthToken = 2 then
         Retval := True;
      --PTR
      --formulation of third condition helps prover
      elsif FirstChar = 'P'
        and LastChar = 'R'
        and BegIdx <= EndIdx - 2
        and LengthToken = 3
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'T' then
            Retval := True;
         else
            RetVal := False;
         end if;
      --SOA
      --formulation of third condition helps prover
      elsif FirstChar = 'S' and
        LastChar = 'A' and
        BegIdx <= EndIdx - 2  and
        LengthToken = 3
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'O' then
            Retval := True;
         else
            RetVal := False;
         end if;
      --SRV
      --formulation of third condition helps prover
      elsif FirstChar = 'S'
        and LastChar = 'V'
        and BegIdx <= EndIdx - 2
        and LengthToken = 3
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'R' then
            Retval := True;
         else
            RetVal := False;
         end if;
      --TXT
      --formulation of third condition helps prover
      elsif FirstChar = 'T'
        and LastChar = 'T'
        and BegIdx <= EndIdx - 2
        and LengthToken = 3
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'X' then
            Retval := True;
         else
            RetVal := False;
         end if;
      --AAAA
      --formulation of third condition helps prover
      elsif FirstChar = 'A'
        and LastChar = 'A'
        and BegIdx <= EndIdx - 3
        and LengthToken = 4
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'A' and
            Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'A' then
            Retval := True;
         else
            RetVal := False;
         end if;

      --NSec
      --formulation of third condition helps prover
      elsif FirstChar = 'N'
        and LastChar = 'C'
        and BegIdx <= EndIdx - 3
        and LengthToken = 4
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'S'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'E'
         then
            Retval := True;
         else
            RetVal := False;
         end if;

      --CName
      --formulation of third condition helps prover
      elsif FirstChar = 'C'
        and LastChar = 'E'
        and BegIdx <= EndIdx - 4 and
        LengthToken = 5
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'N'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'A'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 3)) = 'M'
         then
            Retval := True;
         else
            RetVal := False;
         end if;

      --RRSig
      --formulation of third condition helps prover
      elsif FirstChar = 'R'
        and LastChar = 'G'
        and BegIdx <= EndIdx - 4
        and LengthToken = 5
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'R'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'S'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 3)) = 'I'
         then
            Retval := True;
         else
            RetVal := False;
         end if;

      --DNSKey
      --formulation of third condition helps prover
      elsif FirstChar = 'D'
        and LastChar = 'Y'
        and BegIdx <= EndIdx - 5
        and LengthToken = 6
      then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'N'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'S'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 3)) = 'K'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 4)) = 'E'
         then
            Retval := True;
         else
            Retval := False;
         end if;
      else
         Retval := false;
      end if;
      return Retval;
   end IsRecord;

   --Called only when S(BegIdx..EndIdx) is valid record type indicator
   --For now, only {A, AAAA, CName, DNSKey, MX, Srv, NS, NSec, Ptr, SOA}
   --records supported
   --{RP, TXT recognized but not implemented}
   function GetRecordType
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      EndIdx : in RR_Type.LineLengthIndex)
      return DNS_Types.Query_Type
   is
      FirstChar   : Character;
      LastChar    : Character;
      LengthToken : RR_Type.LineLengthIndex;
      Retval      : DNS_Types.Query_Type;
   begin
      FirstChar := Ada.Characters.Handling.To_Upper (S (BegIdx));
      LastChar := Ada.Characters.Handling.To_Upper (S (EndIdx));
      LengthToken := (EndIdx - BegIdx) + 1;
      --ugly but it gets the job done
      --A
      if FirstChar = 'A' and LengthToken = 1 then
         Retval := DNS_Types.A;
      --NS
      elsif FirstChar = 'N' and LastChar = 'S' and LengthToken = 2 then
         Retval := DNS_Types.NS;
      --MX
      elsif FirstChar = 'M' and LastChar = 'X' and LengthToken = 2 then
         Retval := DNS_Types.MX;
      --RP
      elsif firstChar = 'R' and lastChar = 'P' and lengthToken = 2 then
         Retval := DNS_Types.Unimplemented;
      --Ptr
      --formulation of third condition helps prover
      elsif FirstChar = 'P' and LastChar = 'R' and BegIdx <= EndIdx - 2 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'T' then
            Retval := DNS_Types.Ptr;
         else
            Retval := DNS_Types.Error;
         end if;
      --SOA
      --formulation of third condition helps prover
      elsif FirstChar = 'S' and LastChar = 'A' and BegIdx <= EndIdx - 2 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'O' then
            Retval := DNS_Types.SOA;
         else
            Retval := DNS_Types.Error;
         end if;
      --Srv
      --formulation of third condition helps prover
      elsif FirstChar = 'S' and LastChar = 'V' and BegIdx <= EndIdx - 2 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'R' then
            Retval := DNS_Types.Srv;
         else
            Retval := DNS_Types.Error;
         end if;
      --TXT
      --formulation of third condition helps prover
      elsif FirstChar = 'T' and LastChar = 'T' and BegIdx <= EndIdx - 2 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'X' then
            Retval := DNS_Types.Unimplemented;
         else
            Retval := DNS_Types.Error;
         end if;
      --AAAA
      --formulation of third condition helps prover
      elsif FirstChar = 'A' and LastChar = 'A' and BegIdx <= EndIdx - 3 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'A'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'A'
         then
            Retval := DNS_Types.AAAA;
         else
            Retval := DNS_Types.Error;
         end if;
      --NSec
      --formulation of third condition helps prover
      elsif FirstChar = 'N' and LastChar = 'C' and BegIdx <= EndIdx - 3 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'S'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'E'
         then
            Retval := DNS_Types.NSec;
         else
            Retval := DNS_Types.Error;
         end if;
      --CName
      --formulation of third condition helps prover
      elsif FirstChar = 'C' and LastChar = 'E' and BegIdx <= EndIdx - 4 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'N'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'A'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 3)) = 'M'
         then
            Retval := DNS_Types.CName;
         else
            Retval := DNS_Types.Error;
         end if;
      --RRSig
      --formulation of third condition helps prover
      elsif FirstChar = 'R' and LastChar = 'G' and BegIdx <= EndIdx - 4 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'R'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'S'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 3)) = 'I'
         then
            Retval := DNS_Types.RRSig;
         else
            Retval := Dns_Types.Error;
         end if;
      --DNSKey
      --formulation of third condition helps prover
      elsif FirstChar = 'D' and LastChar = 'Y' and BegIdx <= EndIdx - 5 then
         if Ada.Characters.Handling.To_Upper (S (BegIdx + 1)) = 'N'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 2)) = 'S'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 3)) = 'K'
           and Ada.Characters.Handling.To_Upper (S (BegIdx + 4)) = 'E'
         then
            Retval := DNS_Types.DNSKey;
         else
            Retval := DNS_Types.Error;
         end if;
      else
         Retval := DNS_Types.Unimplemented;
      end if;
      return Retval;
   end GetRecordType;

   procedure CheckAndAppendOrigin
     (Target      : in out RR_Type.DomainNameStringType;
      Origin      : in     RR_Type.DomainNameStringType;
      CurrentLine : in     RR_Type.LineFromFileType;
      LastPos     : in     RR_Type.LineLengthIndex;
      LineCount   : in     Unsigned_Types.Unsigned32;
      Success     : in out Boolean)
   is
   begin
      --if target does not end in '.', append Origin string
      if Target (RR_Type.DomainNameLength (Target)) /= '.'then
         if Origin = RR_Type.BlankDomainName then
            Error_Msgs.PrintBlankOriginWarning (CurrentLine,
                                                LastPos,
                                                LineCount);
         else
            RR_Type.AppendDomainNames (Target, Origin, Success);
            if not Success then
               Error_Msgs.PrintAppendDomainLengthErrorInfo (CurrentLine,
                                                            LastPos,
                                                            LineCount);
            end if;
         end if;
      end if; --check for domain name ending in '.'
   end CheckAndAppendOrigin;

   procedure CheckValidHostName
     (Name    : in     RR_Type.DomainNameStringType;
      Success : in out Boolean)
   is
      Length : RR_Type.DomainNameStringTypeIndex;
      Retval : Boolean := True;
   begin
      --only characters allowed are alphanumerics, '.' and '-'

      Length := RR_Type.DomainNameLength (Name);

      --has to start and end with alphanumeric
      --use length-1 because name(length) is always a period, doesn't count
      --SPARK caught runtime error for length=1, nice!
      if Name (1) = '.'
        or Name (1) = '-'
        or (Length > 1
              and then (Name (Length - 1) = '.'
                          or Name (Length - 1) = '-'))
      then
         Retval := False;
      else
         for I in Integer range 2 .. Length - 2 loop
            --periods must come after alphanumeric
            if Name (I) = '.' then
               if Name (I - 1) = '.' or Name (I - 1) = '-' then
                  Retval := False;
               end if;
               --if not period, must be alphanumeric or underscore
            elsif not Ada.Characters.Handling.Is_Alphanumeric (Name (I))
              and Name (I) /= '-'
            then
               Retval := False;
            end if;
         end loop;
      end if;
      Success := Success and Retval;
   end CheckValidHostName;


   procedure CheckValidSRVOwner
     (Name    : in     RR_Type.DomainNameStringType;
      Success : in out Boolean)
   is
      Length   : Rr_Type.DomainNameStringTypeIndex;
      Retval   : Boolean := True;
      Position : RR_type.DomainNameStringTypeIndex;
   begin
      Length   := RR_Type.DomainNameLength (Name);
      Position := 1;

      -- Srv Records follow the form _service._transportType.Domain

      -- 1. The smallest possible record should be "_x._tcp.x." (10 characters)
      -- 2. The string should start with an underscore
      if Length < 10 or Name (1) /= '_' then
         Retval := False;
      end if;

      -- Find the end of the first set (first occurence of a '.')
      for I in Integer range 2 .. Length - 2 loop
         if Name (I) = '.' then
            Position := I;
            exit;
         end if;
      end loop;

      -- 3. Position of first '.' should be at least 7 characters from the end
      --    of the string
      if Position > Length - 7 then
         Retval := False;
      end if;

      -- 4. Next block must start with an '_'
      if Retval and Position > 1 then
         if Name (Position + 1) /= '_' then
            Retval := False;
         end if;
      else
         Retval := False;
      end if;

      -- Find the end of the second set (secondoccurence of a '.')
      -- for I in Integer range Position+1..Length-2 loop
      --    --# assert true;
      --    if Name(I) = '.' then
      --       position := I;
      --       exit;
      --    end if;
      -- end loop;

      --TestName := Name(Position+1..Length);

      Success := Success and Retval;
   end CheckValidSrvOwner;

   --Just like FindNextToken below , but starts at beginning of line, no index
   --values returned. Only used to see what the first token on the line is.
   procedure FindFirstToken
     (S      : in     RR_Type.LineFromFileType;
      Length : in     RR_Type.LineLengthIndex;
      T      :    out RR_Type.RRItemType)
   is
      BegIdx                 : RR_Type.LineLengthIndex := 1;
      EndIdx                 : RR_Type.LineLengthIndex;
      ContainsOnlyNumbers    : Boolean;
      containsOnlyLetters    : Boolean;
      ContainsPeriod         : Boolean;
      containsColon          : Boolean;
      ContainsDecimalNumbers : Boolean;
      ContainsHexNumbers     : Boolean;
      ContainsLetters        : Boolean;
      --NOTE: Can domain names have anything other than letters, numbers or
      --      periods?
   begin
      while BegIdx < Length
        and then (S (BegIdx) = Blank or S (BegIdx) = Tab)
      loop
         pragma Loop_Invariant (BegIdx >= 1 and BegIdx < Length);
         BegIdx := BegIdx + 1;
      end loop;

      EndIdx := BegIdx;
      while EndIdx < Length
        and then (S (EndIdx) /= Blank
                    and S (EndIdx) /= Tab
                    and S (EndIdx) /= Comment_Char
                    and S (EndIdx) /= L_Paren
                    and S (EndIdx) /= R_Paren)
      loop
         pragma Loop_Invariant
           (BegIdx >= 1 and
            BegIdx <= Length and
            EndIdx >= BegIdx and
            EndIdx < Length);
         EndIdx := EndIdx + 1;
      end loop;
      if (S (EndIdx) = Blank
            or S (EndIdx) = Tab
            or S (EndIdx) = Comment_Char)
        and EndIdx > 1
        and EndIdx > BegIdx
      then
         EndIdx := EndIdx - 1;
      end if;
      ContainsOnlyNumbers := True;
      ContainsOnlyLetters := True;

      ContainsPeriod := False;
      ContainsColon := False;
      ContainsDecimalNumbers := False;
      ContainsHexNumbers := False;
      ContainsLetters := False;

      for I in Integer range BegIdx .. EndIdx loop
         pragma Loop_Invariant
           (BegIdx >= 1 and
            BegIdx <= Length and
            EndIdx >= BegIdx and
            EndIdx <= Length);

         ContainsOnlyNumbers :=
           ContainsOnlyNumbers and Ada.Characters.Handling.Is_Digit (S (I));

         ContainsDecimalNumbers :=
           ContainsDecimalNumbers or Ada.Characters.Handling.Is_Digit (S (I));

         ContainsHexNumbers :=
           ContainsHexNumbers or
           Ada.Characters.Handling.Is_Hexadecimal_Digit (S (I));

         ContainsOnlyLetters :=
           ContainsOnlyLetters and Ada.Characters.Handling.Is_Letter (S (I));

         ContainsLetters :=
           ContainsLetters or Ada.Characters.Handling.Is_Letter(S(I));

         ContainsPeriod := ContainsPeriod or S (I) = '.';
         ContainsColon := ContainsColon or S (I) = ':';
      end loop;

      --figure out what we've got
      if S (BegIdx) = Comment_Char then
         T := RR_Type.Comment;
      elsif S (BegIdx) = Control_Char then
         T := RR_Type.Control;
      elsif S (BegIdx) = L_Paren then
         T := RR_Type.LParen;
      elsif S (BegIdx) = R_Paren then
         T := RR_Type.RParen;
      --@ counts as a domain name, will be replaced with $ORIGIN
      --. counts as domain name, could appear as value of $ORIGIN
      elsif (S (BegIdx) = Origin_Char or S (BegIdx) = '.')
        and BegIdx = EndIdx
      then
         T := RR_Type.DomainNameOrTimeSpec;
      elsif ContainsDecimalNumbers and ContainsOnlyNumbers then
         T := RR_Type.Number;
      elsif ContainsDecimalNumbers
        and ContainsPeriod
        and not ContainsLetters
        and not ContainsColon
      then
         T := RR_Type.IPV4;
      elsif ContainsHexNumbers and ContainsColon and not ContainsPeriod then
         T := RR_Type.IPV6;
      elsif ContainsOnlyLetters and IsClass (S, BegIdx, EndIdx) then
         T := RR_Type.Class;
      elsif ContainsOnlyLetters and IsRecord (S, BegIdx, EndIdx) then
         T := RR_Type.RecordIndicator;
      elsif ContainsLetters then
         T := RR_Type.DomainNameOrTimeSpec;
      elsif BegIdx = Length then  --this means blank line, treated as a comment
         T := RR_Type.Comment;
      else --error of some sort, e.g. invalid class or record type
         T := RR_Type.Other;
      end if;
      --Ada.Text_IO.Put ("TOKEN = " & RrRType.RRItemType'Image(T));
      --Ada.Text_IO.New_Line;
   end FindFirstToken;


   procedure FindNextToken
     (S      : in     RR_Type.LineFromFileType;
      Length : in     RR_Type.LineLengthIndex;
      BegIdx : in out RR_Type.LineLengthIndex;
      EndIdx :    out RR_Type.LineLengthIndex;
      T      :    out RR_Type.RRItemType)
   is
      ContainsOnlyNumbers    : Boolean;
      ContainsOnlyLetters    : Boolean;
      ContainsPeriod         : Boolean;
      ContainsColon          : Boolean;
      ContainsDecimalNumbers : Boolean;
      ContainsHexNumbers     : Boolean;
      ContainsLetters        : Boolean;
      --NOTE:  Can domain names have anything other than letters, numbers or
      --       periods?
   begin
      while BegIdx < Length
        and then (S (BegIdx) = Blank or S (BegIdx) = Tab)
      loop
         pragma Loop_Invariant (BegIdx < Length);
         BegIdx := BegIdx + 1;
      end loop;
      EndIdx := BegIdx;
      while EndIdx < Length
        and then (S (EndIdx) /= Blank
                    and S (EndIdx) /= Tab
                    and S (EndIdx) /= Comment_Char
                    and S (EndIdx) /= L_Paren
                    and S (EndIdx) /= R_Paren
                    and S (EndIdx) /= Origin_Char)
      loop
         pragma Loop_Invariant
           (BegIdx <= Length and EndIdx >= BegIdx and EndIdx < Length);
         EndIdx := EndIdx + 1;
      end loop;
      if (S (EndIdx) = Blank
            or S (EndIdx) = Tab
            or S (EndIdx) = Comment_Char)
        and EndIdx > 1
        and EndIdx > BegIdx
      then
         EndIdx := EndIdx - 1;
      end if;

      ContainsOnlyNumbers := True;
      ContainsOnlyLetters := True;

      ContainsPeriod := False;
      containsColon := False;
      ContainsDecimalNumbers := False;
      ContainsHexNumbers := False;
      ContainsLetters := False;

      for I in Integer range BegIdx..EndIdx loop
         ContainsOnlyNumbers :=
           ContainsOnlyNumbers and S (I) >= '0' and S (I) <= '9';

         pragma Loop_Invariant
           (BegIdx >= 1 and
            BegIdx <= Length and
            EndIdx >= BegIdx and
            EndIdx <= Length and
            EndIdx = EndIdx'Loop_Entry and
            (if ContainsOnlyNumbers then
               (for all J in integer range BegIdx .. I =>
                  S (J) >= '0' and S (J) <= '9')));
         ContainsDecimalNumbers :=
           ContainsDecimalNumbers or (S (I) >= '0' and S(I) <= '9');

         ContainsHexNumbers :=
           ContainsHexNumbers or
           Ada.Characters.Handling.Is_Hexadecimal_Digit (S (I));

         ContainsOnlyLetters :=
           ContainsOnlyLetters and
           Ada.Characters.Handling.Is_Letter (S (I));

         ContainsLetters :=
           ContainsLetters or Ada.Characters.Handling.Is_Letter (S (I));

         ContainsPeriod := ContainsPeriod or S (I) = '.';
         ContainsColon := ContainsColon or S (I) = ':';
      end loop;

      --figure out what we've got
      if S (BegIdx) = Comment_Char then
         T := RR_Type.Comment;
      elsif S (BegIdx) = Control_Char then
         T := RR_Type.Control;
      elsif S (BegIdx) = L_Paren then
         T := RR_Type.LParen;
      elsif S (BegIdx) = R_Paren then
         T := RR_Type.RParen;
      --@ counts as a domain name, will be replaced with $ORIGIN
      --. counts as domain name, could appear as value of $ORIGIN
      elsIf (S (BegIdx) = Origin_Char or S (BegIdx) = '.')
        and BegIdx = EndIdx
      then
         T := RR_Type.DomainNameOrTimeSpec;
      elsif ContainsOnlyNumbers then
         T := RR_Type.Number;
      elsif ContainsDecimalNumbers
        and ContainsPeriod
        and not ContainsLetters
        and not ContainsColon
      then
         T := RR_Type.IPV4;
      elsif ContainsHexNumbers
        and ContainsColon
        and not ContainsPeriod
      then
         T := RR_Type.IPV6;
      elsif ContainsOnlyLetters and IsClass (S, BegIdx, EndIdx) then
         T := RR_Type.Class;
      elsif ContainsOnlyLetters and IsRecord (S, BegIdx, EndIdx) then
         T := RR_Type.RecordIndicator;
      elsif ContainsLetters then
         T := RR_Type.DomainNameOrTimeSpec;
      elsif BegIdx = Length then  --this means blank line, treated as a comment
         T := RR_Type.Comment;
      else --error of some sort, e.g. invalid class or record type
         T := RR_Type.Other;
      end if;
   end FindNextToken;

   --true if Char is s,m,h,d,w or uppercase equivalent
   function IsMult (Char: in Character) return Boolean is
      C      : Character;
      Retval : boolean;
   begin
      C := Ada.Characters.Handling.To_Upper (Char);
      if C = 'S' or C = 'M' or C = 'H' or C = 'D' or C = 'W' then
         Retval := True;
      else
         Retval := False;
      end if;
      return Retval;
   end IsMult;

   procedure Convert8BitUnsigned
     (Value        :    out Unsigned_Types.Unsigned8;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      BegIdx       : in     RR_Type.LineLengthIndex;
      EndIdx       : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      DigitVal : Natural;
      TmpVal   : Natural;
   begin
      TmpVal := 0;
      Value := 0;
      for I in Integer range BegIdx .. EndIdx loop
         pragma Loop_Invariant
           (BegIdx >= 1 and
            TmpVal <= Unsigned_Types.Max_8Bit_Val);

         DigitVal := Character'Pos (ZoneFileLine (I)) - Character'Pos ('0');
         TmpVal := 10*TmpVal + DigitVal;
         exit when TmpVal > Unsigned_Types.Max_8Bit_Val;
      end loop;
      --make sure it's not too big
      if TmpVal > Unsigned_Types.Max_8Bit_Val then
         Success := False;
      else --have a valid preference value
         Value := Unsigned_Types.Unsigned8 (TmpVal);
      end if;
   end Convert8BitUnsigned;

   procedure Convert16BitUnsigned
     (Value        :    out Unsigned_Types.Unsigned16;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      BegIdx       : in     RR_Type.LineLengthIndex;
      EndIdx       : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      DigitVal : Natural;
      TmpVal   : Natural;
   begin
      TmpVal := 0;
      Value := 0;
      for I in Integer range BegIdx .. EndIdx loop
         pragma Loop_Invariant
           (BegIdx >= 1 and
            TmpVal <= Unsigned_Types.Max_16Bit_Val);
         DigitVal := Character'Pos (ZoneFileLine (I)) - Character'Pos ('0');
         TmpVal := 10*TmpVal + DigitVal;

         exit when Tmpval > Unsigned_Types.Max_16Bit_Val;
      end loop;
      --make sure it's not too big
      if TmpVal > Unsigned_Types.Max_16Bit_Val then
         Success := False;
      else --have a valid 16-bit value
         Value := Unsigned_Types.Unsigned16 (TmpVal);
      end if;
   end Convert16BitUnsigned;

   procedure Convert32BitUnsigned
     (Value        :    out Unsigned_Types.Unsigned32;
      ZoneFileLine : in     RR_Type.LineFromFileType;
      BegIdx       : in     RR_Type.LineLengthIndex;
      EndIdx       : in     RR_Type.LineLengthIndex;
      Success      : in out Boolean)
   is
      DigitVal : Long_Long_Integer;
      TmpVal   : Long_Long_Integer;
   begin
      TmpVal := 0;
      Value := 0;
      for I in Integer range BegIdx .. EndIdx loop
         pragma Loop_Invariant
           (BegIdx >= 1 and
            TmpVal >= 0 and
            TmpVal <= Unsigned_Types.Max_32Bit_Val);
         DigitVal := Character'Pos (ZoneFileLine (I)) - Character'Pos ('0');
         TmpVal := 10*TmpVal + DigitVal;
         exit when TmpVal > Unsigned_Types.Max_32Bit_Val;
      end loop;
      --make sure it's not too big
      if TmpVal > unsigned_types.Max_32Bit_Val then
         Success := False;
      else --have a valid 32-bit value
         Value := Unsigned_Types.Unsigned32 (TmpVal);
      end if;
   end Convert32BitUnsigned;

   --converts the time specifier at S (BegIdx .. EndIdx) into a time value in
   --seconds, returned in RetVal.
   --a time specifier is either a Num or one or more Blobs.  A Num is a string
   --of decimal digits.
   --A Blob is a Num followed by a Mult.  A Mult is one of {s,m,h,w,d} and
   --their upper-case equivalents.
   --Sets Success to false if the time specifier is invalid
   procedure ConvertTimeSpec
     (S       : in     RR_Type.LineFromFileType;
      BegIdx  : in     RR_Type.LineLengthIndex;
      EndIdx  : in     RR_Type.LineLengthIndex;
      RetVal  :    out Unsigned_Types.Unsigned32;
      Success : in out Boolean)
   is
      Tmp         : Long_Long_Integer := 0;
      Blob        : Long_Long_Integer := 0;
      CurrentChar : Character;

      function MultValue (Char : in Character) return natural
        with Pre  => IsMult (Char),
             Post => MultValue'Result >= 0 and
                     MultValue'Result <= 60 * 60 * 24 * 7
      is
         C      : Character;
         RetVal : Natural;
      begin
         C := Ada.Characters.Handling.To_Upper(Char);
         case C is
            when 'S' =>
               RetVal := 1;
            when 'M' =>
               RetVal := SecondsInAMinute;
            when 'H' =>
               RetVal := SecondsInAMinute*MinutesInAnHour;
            when 'D' =>
               RetVal := (SecondsInAMinute*MinutesInAnHour)*HoursInADay;
            when 'W' =>
               RetVal :=
                 ((SecondsInAMinute*MinutesInAnHour)*HoursInADay)*DaysInAWeek;
            when others =>
               RetVal := 0;   --will never happen if precondition is met
         end case;
         return RetVal;
      end MultValue;

   begin
      for I in Integer range BegIdx .. EndIdx loop
         pragma Loop_Invariant
           (Blob >= 0 and
            Blob <= RR_Type.SOA_Record_Type.Max_Time_Val and
            Tmp >= 0 and
            Tmp <= RR_Type.SOA_Record_Type.Max_Time_Val);
         CurrentChar := S (I);
         if CurrentChar >= '0' and CurrentChar <= '9' then
            Blob := 10*Blob + (Character'Pos (CurrentChar)-Character'Pos ('0'));
            if Blob > RR_Type.SOA_Record_Type.Max_Time_Val then
               Success := False;
            end if;
         elsif IsMult (CurrentChar) then
            if Blob = 0 then
               Success := False;
            else
               Blob := Blob*Long_Long_Integer (MultValue (CurrentChar));
               Tmp := Tmp + Blob;
               if Blob > RR_Type.SOA_Record_Type.Max_Time_Val
                 or Tmp > RR_Type.SOA_Record_Type.Max_Time_Val
               then
                  Success := False;
               end if;
               Blob := 0;
            end if;
         else
            Success := False;
         end if;
         exit when Success = False;
      end loop;
      if not Success then
         Tmp := 0;
      elsif Tmp = 0 then  --handle case when time specifier is just a number
                          --(no mult)
         Tmp := Blob;
      end if;
      RetVal := Unsigned_Types.Unsigned32 (Tmp);
   end ConvertTimeSpec;

   procedure ConvertTimeString
     (TimeVal    :    out Unsigned_Types.Unsigned32;
      TimeString : in     RR_Type.RRSig_Record_Type.TimeStringType;
      Success    : in out boolean)
   is
      Year   : Natural := 0;
      Month  : Natural := 0;
      Day    : Natural := 0;
      Hour   : Natural := 0;
      Minute : Natural := 0;
      Second : Natural := 0;
      Num    : Natural;
   begin
      for I in RR_Type.RRSig_Record_Type.TimeStringTypeIndex loop
         --help the prover show these values remain in type
         pragma Loop_Invariant
           (Year <= RR_Type.RRSig_Record_Type.Max_Year and
            Month <= 12 and
            Day <= 31 and
            Hour <= 23 and
            Minute <= 59 and
            Second <= 59);
         Num := Character'Pos (TimeString (I))- Character'Pos ('0');
         if I <= 4 then
            Year := 10 * Year + Num;
         elsif I <= 6 then
            Month := 10 * Month + Num;
         elsif I <= 8 then
            Day:= 10 * Day + Num;
         elsif I <= 10 then
            Hour := 10 * Hour + Num;
         elsif I <= 12 then
            Minute:= 10 * Minute + Num;
         elsif I <= 14 then --flagged, but leave as is in case
                            --TimeStringTypeIndex ever changed
            Second := 10 * Second + Num;
         end if;
         exit when Year > RR_Type.RRSig_Record_Type.Max_Year or
                   Month > MonthsInAYear or
                   Day > MaxDaysInAMonth or
                   Hour >= HoursInADay or
                   Minute >= MinutesInAnHour or
                   Second >= SecondsInAMinute;
      end loop;
      if Year > RR_Type.RRSig_Record_Type.Max_Year
        or Month > MonthsInAYear
        or Day > MaxDaysInAMonth
        or Hour >= HoursInADay
        or Minute >= MinutesInAnHour
        or Second >= SecondsInAMinute
      then
         Success := False;
         TimeVal := 0;
      else
         TimeVal := Non_Spark_Stuff.Get_Time_Of (Year,
                                                 Month,
                                                 Day,
                                                 Hour,
                                                 Minute,
                                                 Second);
      end if;
   end ConvertTimeString;

   procedure AddToKeyR
     (RRSig_Rec : in out RR_Type.RRSig_Record_type.RRSigRecordType;
      S         : in     RR_Type.LineFromFileType;
      Length    : in     RR_Type.LineLengthIndex;
      AllDone   :    out Boolean;    --this is needed because line might
                                     --terminate with ')'
      Success   : in out Boolean)
   is
      BegIdx       : RR_Type.LineLengthIndex;
      EndIdx       : RR_Type.LineLengthIndex;
      ReturnedType : RR_type.RRItemType;
   begin
      --find start of key fragment
      BegIdx := 1;
      while BegIdx < Length
        and then (S (BegIdx) = Blank or S (BegIdx) = Tab)
      loop
         pragma Loop_Invariant (BegIdx >= 1 and BegIdx < Length);
         BegIdx := BegIdx + 1;
      end loop;

      --find end of key fragment
      EndIdx := BegIdx;
      while EndIdx < Length
        and then (S (EndIdx) /= Blank and S (EndIdx) /= Tab)
      loop
         pragma Loop_Invariant
           (BegIdx >= 1 and
            BegIdx <= EndIdx and
            EndIdx >= 1 and
            EndIdx < Length);
         EndIdx:= EndIdx + 1;
      end loop;

      --check if key too long
      if RRSig_Rec.SignatureLength + ((EndIdx - BegIdx) + 1) >
           RR_Type.RRSig_Record_Type.MaxRRSigLength
      then
         Success := False;
      else
         --add key fragment on to key field of record
         for I in Integer range BegIdx .. EndIdx loop
            pragma Loop_Invariant
              (BegIdx = begIdx'Loop_Entry and
               EndIdx = EndIdx'Loop_Entry and
               I >= BegIdx and
               I <= EndIdx and
               BegIdx >= 1 and
               RRSig_Rec.SignatureLength + ((EndIdx - BegIdx) + 1) <=
                 RR_Type.RRSig_Record_Type.MaxRRSigLength);
            RRSig_Rec.Signature
              (RRSig_Rec.SignatureLength + ((I - BegIdx) + 1)) := S (I);
         end loop;
         --update signature length
         RRSig_Rec.SignatureLength := RRSig_Rec.SignatureLength +
                                      ((EndIdx - BegIdx) + 1);
      end if;

      --SPARK caught runtime error if no ')', nice!
      if EndIdx < Length then
         BegIdx := EndIdx + 1;
         FindNextToken (S, Length, BegIdx, EndIdx, ReturnedType);

         if ReturnedType = RR_Type.RParen and BegIdx <= EndIdx then
            AllDone := True;
         else
            AllDone := False;   --makes flow error go away
         end if;
      else   --nothing after the key fragment, need to keep going
         AllDone := False;
      end if;
   end AddToKeyR;

   procedure AddToKey
     (DNSKEY_Rec : in out RR_Type.DNSKey_Record_Type.DNSKeyRecordType;
      S          : in     RR_Type.LineFromFileType;
      Length     : in     RR_Type.LineLengthIndex;
      Success    : in out Boolean)
   is
      BegIdx : RR_Type.LineLengthIndex;
      EndIdx : RR_Type.LineLengthIndex;
   begin
      --find start of key fragment
      BegIdx := 1;
      while BegIdx < Length
        and then (S (BegIdx) = Blank or S (BegIdx) = Tab)
      loop
         pragma Loop_Invariant (BegIdx >= 1 and BegIdx < Length);
         BegIdx := BegIdx + 1;
      end loop;

      --find end of key fragment
      EndIdx := BegIdx;
      while EndIdx < Length
        and then (S (EndIdx) /= Blank and S (EndIdx) /= Tab)
      loop
         pragma Loop_Invariant
           (BegIdx >= 1 and
            BegIdx <= EndIdx and
            EndIdx >= 1 and
            EndIdx < Length);
         EndIdx:= EndIdx + 1;
      end loop;

      --check if key too long
      if DNSKey_Rec.KeyLength + ((EndIdx - BegIdx) + 1) >
           RR_Type.DNSKey_Record_Type.MaxDNSKeyLength
      then
         Success := False;
      else
         --add key fragment on to key field of record
         for I in Integer range BegIdx .. EndIdx loop
            pragma Loop_Invariant
              (BegIdx = BegIdx'Loop_Entry and
               EndIdx = EndIdx'Loop_Entry and
               I >= BegIdx and
               I <= EndIdx and
               BegIdx >= 1 and
               DNSKey_Rec.KeyLength + ((EndIdx - BegIdx)+1) <=
                 RR_Type.DNSKey_Record_Type.MaxDNSKeyLength);
            DNSKey_Rec.Key (DNSKey_Rec.KeyLength + ((I - BegIdx) + 1)) := S (I);
         end loop;
         --update key length
         DNSKey_Rec.KeyLength := DNSKey_Rec.KeyLength + ((EndIdx - BegIdx) + 1);
      end if;
   end AddToKey;

   --convert IPV6 address at S (BegIdx .. EndIdx) into 8 unsigned 16-bit
   --integers expects eight valid 16-bit hex numbers separated by colons
   --returns Invalid_IPV6_Addr if conversion unsuccessful
   function ConvertIPV6
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      EndIdx : in RR_Type.LineLengthIndex)
      return RR_Type.AAAA_Record_Type.IPV6AddrType
   is
      Num_Fields         : constant Natural := 8;
      Req_Num_Separators : constant Natural := Num_Fields-1;
      Field_Separator    : constant Character := ':';
      subtype SeparatorIndexType is Integer
        range 1 .. Req_Num_Separators + 1;
      --could go one higher if processing bad IP

      type SeparatorIndexArrayType is array (SeparatorIndexType)
        of RR_Type.LineLengthIndex;

      Max_Digits_In_Field : constant Natural := 4;
      IPV6_Radix          : constant Unsigned_Types.Unsigned16 := 16;

      SeparatorIndexArray : SeparatorIndexArrayType :=
        SeparatorIndexArrayType'(others => 1);

      Ctr                 : RR_Type.LineLengthIndex;
      NumSeparators       : Natural;
      FieldTotal          : Unsigned_Types.Unsigned16;
      NumDigitsInField    : Natural;

      RetVal              : RR_Type.AAAA_Record_Type.IPV6AddrType :=
        RR_Type.AAAA_Record_Type.Invalid_IPV6_Addr;

      function SeparatorsOK
        (Line   : in RR_Type.LineFromFileType;
         SArray : in SeparatorIndexArrayType)
         return Boolean
      is
      begin
         --no need to check the last entry, that will have been detected
         --elsewhere
         for I in SeparatorIndexType'First .. SeparatorIndexType'Last - 1 loop
            if Line (SArray (I)) /= Field_Separator
              or SArray (I) = SArray (I + 1) - 1
            then
               return False;
            end if;
         end loop;
         return True;
      end SeparatorsOK;

   begin
      Ctr              := BegIdx;
      NumSeparators    := 0;
      FieldTotal       := 0;
      NumDigitsInField := 0;

      while Ctr < EndIdx
        and then (NumSeparators <= Req_Num_Separators
                    and NumDigitsInField <= Max_Digits_In_Field)
      loop
         pragma Loop_Variant (Increases => Ctr);
         pragma Loop_Invariant
           (Ctr < EndIdx and
            NumSeparators <= Req_Num_Separators and
            NumDigitsInField <= Max_Digits_In_Field);
         if Ada.Characters.Handling.Is_Decimal_Digit (S (Ctr)) then
            FieldTotal := IPV6_Radix*FieldTotal +
                          (Character'Pos (S (Ctr)) - Character'Pos ('0'));
            NumDigitsInField := NumDigitsInField + 1;
         elsif Ada.Characters.Handling.Is_Hexadecimal_Digit (S (Ctr)) then
            FieldTotal := IPV6_Radix*FieldTotal +
              (Character'Pos (Ada.Characters.Handling.To_Upper (S (Ctr))) -
                 Character'Pos ('A')) + 10;
            NumDigitsInField := NumDigitsInField +1;
         else
            NumSeparators := NumSeparators + 1;
            SeparatorIndexArray (NumSeparators) := Ctr;
            RetVal (NumSeparators) := FieldTotal;
            FieldTotal := 0;
            NumDigitsInField := 0;
         end if;
         Ctr := Ctr + 1;
      end loop;
      --EndIdx might be the maximum value possible, so must catch last
      --character here
      if Ctr = EndIdx and NumSeparators <= Req_Num_Separators then
         if Ada.Characters.Handling.Is_Decimal_Digit (S (Ctr)) then
            FieldTotal := IPV6_Radix*FieldTotal +
                          (Character'Pos (S (Ctr)) - Character'Pos ('0'));
            NumDigitsInField := NumDigitsInField + 1;
            RetVal (NumSeparators + 1) := FieldTotal;
         elsif Ada.Characters.Handling.Is_Hexadecimal_Digit (S (Ctr)) then
            FieldTotal := IPV6_Radix*FieldTotal +
              (Character'Pos (Ada.Characters.Handling.To_Upper (S (Ctr))) -
                 Character'Pos ('A')) + 10;
            NumDigitsInField := NumDigitsInField + 1;
            RetVal (NumSeparators + 1) := FieldTotal;
         else  --if last character is anything but an integer, force an error
            NumSeparators := Num_Fields;
         end if;
      end if;

      if not (SeparatorsOK (S, SeparatorIndexArray)
                and NumSeparators = Req_Num_Separators
                and NumDigitsInField <= Max_Digits_In_Field)
      then
         RetVal := RR_Type.AAAA_Record_Type.Invalid_IPV6_Addr;
      end if;

      return RetVal;
   end ConvertIpv6;

   --convert IPV4 address at S (BegIdx .. EndIdx) into a 32-bit number
   --returns 0 if conversion unsuccessful
   function ConvertIPV4
     (S      : in RR_Type.LineFromFileType;
      BegIdx : in RR_Type.LineLengthIndex;
      EndIdx : in RR_Type.LineLengthIndex)
     return Unsigned_Types.Unsigned32
   is
      Num_Bytes           : constant Natural := 4;
      Req_Num_Separators  : constant Natural := Num_Bytes - 1;
      Byte_Separator      : constant Character := '.';
      subtype SeparatorIndexType is Integer range 1 .. Req_Num_Separators + 1;
      --could go one higher if processing bad ip

      type SeparatorIndexArrayType is array (SeparatorIndexType)
        of RR_Type.LineLengthIndex;

      Max_Byte_Value      : constant Unsigned_Types.Unsigned32 := 255;
      Max_Digits_Per_Byte : constant Natural := 3;
      IPV4_Radix          : constant unsigned_types.unsigned32:= 10;

      SeparatorIndexArray : SeparatorIndexArrayType :=
        SeparatorIndexArrayType'(others => 1);

      Ctr                 : RR_Type.LineLengthIndex;
      NumSeparators       : Natural;
      ByteTotal           : Unsigned_Types.Unsigned32;
      NumDigitsInByte     : Natural;
      GrandTotal          : Unsigned_Types.Unsigned32;
      RetVal              : Unsigned_Types.Unsigned32;

      function SeparatorsOK
        (Line   : in RR_Type.LineFromFileType;
         SArray : in SeparatorIndexArrayType)
         return Boolean
      is
         RetVal : Boolean;
      begin
         if Line (SArray (1)) = Byte_Separator
           and Line (SArray (2)) = Byte_Separator
           and Line (SArray (3)) = Byte_Separator
           and SArray (1) /= SArray (2) - 1
           and SArray (2) /= SArray (3) - 1
         then
            RetVal := True;
         else
            RetVal := False;
         end if;
         return RetVal;
      end SeparatorsOK;

   begin
      Ctr := BegIdx;
      NumSeparators := 0;
      ByteTotal := 0;
      NumDigitsInByte := 0;
      GrandTotal := 0;
      while Ctr < EndIdx
        and then (NumSeparators <= Req_Num_Separators
                    and ByteTotal <= Max_Byte_Value
                    and NumDigitsInByte <= Max_Digits_Per_Byte)
      loop
         pragma Loop_Variant (Increases => Ctr);
         pragma Loop_Invariant
           (Ctr < EndIdx and
            NumSeparators <= Req_Num_Separators and
            NumDigitsInByte <= Max_Digits_Per_Byte);
         if Ada.Characters.Handling.Is_Digit (S (Ctr)) then
            ByteTotal := IPV4_Radix * ByteTotal +
                         (Character'Pos (S (Ctr)) - Character'Pos ('0'));
            NumDigitsinbyte := NumDigitsInByte + 1;
         else
            NumSeparators := NumSeparators + 1;
            SeparatorIndexArray (NumSeparators) := Ctr;
            GrandTotal := (Max_Byte_Value + 1) * GrandTotal + ByteTotal;
            ByteTotal := 0;
            NumDigitsInByte := 0;
         end if;
         Ctr := Ctr + 1;
      end loop;

      --EndIdx might be the maximum value possible, so must catch last
      --character here
      if Ctr = EndIdx then
         if Ada.Characters.Handling.Is_Digit(S(Ctr)) then
            ByteTotal := 10 * ByteTotal +
                         (Character'Pos (S (Ctr)) - Character'Pos ('0'));
            NumDigitsinbyte := NumDigitsInByte + 1;
            GrandTotal := (Max_Byte_Value + 1) * GrandTotal + ByteTotal;
         else  --if last character is anything but an integer, force an error
            NumSeparators := Num_Bytes;
         end if;
      end if;
      if SeparatorsOK (S, SeparatorIndexArray)
        and NumSeparators = Req_Num_Separators
        and NumDigitsInByte <= Max_Digits_Per_Byte
        and ByteTotal <= Max_Byte_Value
      then
         RetVal := GrandTotal;
      else
         RetVal := RR_Type.A_Record_Type.Invalid_IPV4_Addr;
      end if;
      return RetVal;
   end ConvertIpv4;

end Parser_Utilities;
