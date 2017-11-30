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
-- Description:
--    Message to and from SPRE are ASCII strings.
--    This package provides the utilities for extracting
--    the string relating to a particular parameter.
--    This string can then be converted to the relevant type by the
--    caller.
--    Parameters are passed in two ways:
--      ** As a 'Value' in a list (possibly of one), in which case
--         GetStringByPos should be used to extract it; or
--      ** As a 'Key':'Value' pair in a dictionary, when
--         GetStringByKey should be used once the dictionary has been
--         extracted using GetDictionary.
--
------------------------------------------------------------------

with TcpIp,
     CommonTypes;

package MsgProc is

   type DictionaryT is new String;

   ------------------------------------------------------------------
   -- GetStringByPos
   --
   -- Description:
   --    Extracts the value corresponding to the position given by Arg.
   --    If the string is not found in full, then a null string is returned.
   --
   --    Assumes that there are no dictionaries preceding this parameter in
   --    Msg. If there are, the dictionary should be removed first, and
   --    Arg calculated accordingly.
   --    If a preceding parameter is a 'list', then each element of that
   --    list should be considered seperately when calculating Arg.
   ------------------------------------------------------------------
   function GetStringByPos (Msg : String;
                            Arg : Positive)
                           return String;

   ------------------------------------------------------------------
   -- GetDictionary
   --
   -- Description:
   --    Extracts the 'arg'th dictionary from Msg. Note that the return
   --    string does not include the enclosing braces.
   --
   ------------------------------------------------------------------
   function GetDictionary (Msg : String;
                           Arg : Positive)
                          return DictionaryT;

   ------------------------------------------------------------------
   -- GetStringByKey
   --
   -- Description:
   --    Extracts the value corresponding to the Key, from Dic.
   --    If the string is not found in full, then a null string is returned.
   --
   ------------------------------------------------------------------
   function GetStringByKey (Dic : DictionaryT;
                            Key : String)
                           return String;

   ------------------------------------------------------------------
   -- GetDictionaryByKey
   --
   -- Description:
   --    Extracts the dictionary corresponding to the Key, from Dic.
   --
   ------------------------------------------------------------------
   function GetDictionaryByKey (Dic : DictionaryT;
                                Key : String)
                               return DictionaryT;

   ------------------------------------------------------------------
   -- GetResponseFromMsg
   --
   -- Description:
   --    Removes SPREs response code from Msg.Data and returns the remaining
   --    String.
   --
   ------------------------------------------------------------------
   function GetResponseFromMsg (Msg : in     TcpIp.MessageT) return String;

   ------------------------------------------------------------------
   -- StringFrom32
   --
   -- Description:
   --    Converts an unsigned 32-bit number into a string.
   --
   ------------------------------------------------------------------
   function StringFrom32 (Num : in     CommonTypes.Unsigned32T) return String;

   ------------------------------------------------------------------
   -- StringFromInt
   --
   -- Description:
   --    Converts an integer into a string.
   --
   ------------------------------------------------------------------
   function StringFromInt (Int : in     Integer) return String;

end MsgProc;
