------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

------------------------------------------------------------------
-- MsgProc
--
-- Implementation notes:
--    None.
--
------------------------------------------------------------------

with Ada.Strings;
with Ada.Strings.Fixed;

package body MsgProc
  with SPARK_Mode => Off  --  exception handlers
is

   ------------------------------------------------------------------
   -- GetStringByPos
   --
   -- Implementation Notes:
   --    Assumes the response code has been removed.
   --
   --    Performed by searching for single quotes.
   --    Will not work any responses include additional single quotes.
   --
   ------------------------------------------------------------------
   function GetStringByPos (Msg : String;
                            Arg : Positive)
                           return String
   is
      ValStart, ValFin : Natural;
      LocalMsg         : String := Msg;
   begin

      -- Now loop through the list of arguments, deleting each
      -- as we find it
      for i in 1 .. Arg loop

         ValStart := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                             Pattern => "'");

         Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                                  From    => 1,
                                  Through => ValStart);

         -- If closing quote is not found, return null string
         ValFin := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                           Pattern => "'");

         if i /= Arg then
            Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                                     From    => 1,
                                     Through => ValFin);
         end if;
      end loop;

      return LocalMsg (1 .. ValFin-1);
   end GetStringByPos;

   ------------------------------------------------------------------
   -- GetDictionary
   --
   -- Implementation Notes:
   --    Performed by searching for open and close braces.
   --
   ------------------------------------------------------------------
   function GetDictionary (Msg : String;
                           Arg : Positive)
                          return DictionaryT is
      DicStart,
      DicFin,
      PrimaryCount,
      SecondaryCount : Natural := 0;
      PrimaryOpen    : Boolean := False;
      LocalReturn    : String := Msg;
   begin
      -- Search for the required dictionary, given by Arg.
      for i in 1 .. Msg'Length loop
         if Msg (i) = '{' then
            -- Found a dictionary start
            -- Is it a dictionary at the highest level?
            if not PrimaryOpen then
               PrimaryOpen := True;
               PrimaryCount := PrimaryCount + 1;
               -- Is this the dictionary we want?
               if PrimaryCount = Arg then
                  DicStart := i;
               end if;
            else
               -- an internal dictionary, increment count
               SecondaryCount := SecondaryCount + 1;
            end if;

         elsif Msg (i) = '}' then
            -- Found a dictionary end
            -- Is there an internal dictionary to close?
            if SecondaryCount /= 0 then
               SecondaryCount := SecondaryCount - 1;
            else
               PrimaryOpen := False;
               -- Is this the end of the dictionary we want?
               if PrimaryCount = Arg then
                  DicFin := i;
                  exit;
               end if;
            end if;
         end if;
      end loop;

      Ada.Strings.Fixed.Move
        (Source => Msg(DicStart+1 .. DicFin-1),
         Target => LocalReturn);

      return DictionaryT(LocalReturn(1..DicFin - 1 - DicStart));
   end GetDictionary;

   ------------------------------------------------------------------
   -- GetStringByKey
   --
   -- Implementation notes:
   --    Perform get by searching for the correct key, and then extracting
   --    the string within the next two single quotes.
   --    For this to work, ALL parameters in the reply must be of the form
   --    'Key' : 'Value' or 'Key' : {Dic}.
   --
   ------------------------------------------------------------------
   function GetStringByKey (Dic : DictionaryT;
                            Key : String)
                           return String
   is
      ValStart,
      ValFin,
      KeyStart  : TcpIp.MessageLengthT := 0;
      LocalMsg  : String := String(Dic);
   begin
      loop
         KeyStart := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                             Pattern => Key);

         if KeyStart /= 0 then
            -- Found the Key string - is it enclosed by single quotes?
            if LocalMsg(KeyStart - 1) = ''' and
               LocalMsg(KeyStart + Key'Length) = ''' then

               exit;

            else
               -- What we found was not the key - delete everything up to
               -- this point and search again.
               Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                                        From    => 1,
                                        Through => KeyStart + Key'Length);
            end if;
         else
            -- Did not find the key - return null string
            exit;

         end if;
      end loop;

      if KeyStart /= 0 then
         -- should delete everything up to the key and its enclosing quote.
         Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                                  From    => 1,
                                  Through => KeyStart + Key'Length);

         ValStart := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                             Pattern => "'");

         Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                                  From    => 1,
                                  Through => ValStart);

         -- If closing quote is not found, return null string
         ValFin := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                           Pattern => "'") - 1;

      end if; -- else key does not appear, return null string

      return LocalMsg (1 .. ValFin);

   exception
      when E : others =>
         return "";
   end GetStringByKey;

   ------------------------------------------------------------------
   -- GetDictionaryByKey
   --
   -- Implementation notes:
   --    Perform get by searching for the correct key, and then extracting
   --    the string within the next two (matching) braces.
   --    For this to work, ALL parameters in the reply must be of the form
   --    'Key' : 'Value' or 'Key' : {Dic}.
   --
   ------------------------------------------------------------------
   function GetDictionaryByKey (Dic : DictionaryT;
                                Key : String)
                               return DictionaryT
   is
      KeyStart : TcpIp.MessageLengthT := 0;
      LocalMsg : String := String(Dic);
   begin

      loop
         KeyStart := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                             Pattern => Key);

         if KeyStart /= 0 then
            -- Found the Key string - is it enclosed by single quotes?
            if LocalMsg(KeyStart - 1) = ''' and
               LocalMsg(KeyStart + Key'Length) = ''' then

               -- We've found the Key - exit search loop
               exit;

            else
               -- What we found was not the key - delete everything up to
               -- this point and search again.
               Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                                        From    => 1,
                                        Through => KeyStart + Key'Length);
            end if;
         else
            -- Did not find the key - return null string
            exit;

         end if;
      end loop;

      if KeyStart /= 0 then

         -- Delete everything up to the key.
         Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                                  From    => 1,
                                  Through => KeyStart + Key'Length);

         return GetDictionary(Msg => LocalMsg,
                              Arg => 1);

      else -- key does not appear, return null string
         return "";
      end if;

   exception
      when E : others =>
         return "";
   end GetDictionaryByKey;

   ------------------------------------------------------------------
   -- GetResponseFromMsg
   --
   -- Implementation Notes:
   --    SPREs response code is the first 'string'.
   --
   ------------------------------------------------------------------
   function GetResponseFromMsg (Msg : in     TcpIp.MessageT) return String
   is
      CodeStart, CodeFin : Natural;
      LocalMsg           : String := Msg.Data(1..Msg.Length);
   begin

      -- Locally remove the SPRE response code...
      CodeStart := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                           Pattern => "'");

      -- delete start '
      Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                               From    => CodeStart,
                               Through => CodeStart);

      CodeFin := Ada.Strings.Fixed.Index(Source  => LocalMsg,
                                         Pattern => "'");

      -- delete from code start to end '
      Ada.Strings.Fixed.Delete(Source  => LocalMsg,
                               From    => CodeStart,
                               Through => CodeFin);

      return LocalMsg;

   exception
      when E : others =>
         return "";
   end GetResponseFromMsg;

   ------------------------------------------------------------------
   -- StringFrom32
   --
   -- Implementation Notes:
   --    Trims the image of the number.
   --
   ------------------------------------------------------------------
   function StringFrom32 (Num : CommonTypes.Unsigned32T) return String is
   begin
      return Ada.Strings.Fixed.Trim
        (CommonTypes.Unsigned32T'Image(Num), Ada.Strings.Both);
   end StringFrom32;

   ------------------------------------------------------------------
   -- StringFromInt
   --
   -- Implementation Notes:
   --    Trims the image of the number.
   --
   ------------------------------------------------------------------
   function StringFromInt (Int : Integer) return String is
   begin
      return Ada.Strings.Fixed.Trim(Integer'Image(Int), Ada.Strings.Both);
   end StringFromInt;

end MsgProc;
