-------------------------------------------------------------------------------
-- Copyright: Omlis Ltd. 2014.  All rights reserved.
--
-- Omlis Confidential.
-- All information contained herein is and remains the property of Omlis Ltd.
-- The intellectual and technical concepts contained herein are proprietary to
-- Omlis Ltd. and may be covered by Patents or Patents in process and are
-- protected by trade secret or copyright law.  Dissemination of this material
-- or reproduction of this material is strictly forbidden unless prior written
-- permission is obtained from Omlis Ltd.
--
--  Decription:
--     This module defines types used throughout the remainder of the
--     development.
--
---------------------------------------------------------------------------

with Ada.Unchecked_Conversion;
with CommonTypes;
use type CommonTypes.LongLongWord_t;
with Interfaces;
use type Interfaces.Unsigned_32;

package body CommonTypes
is

   ---------------------------------------------
   --  Description:
   --    Conversion from Bytes to Words
   --
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Convert is new Ada.Unchecked_Conversion
     (Source => ByteArray32_t,
      Target => WordArray16_t);

   ---------------------------------------------
   --  Description:
   --    Conversion from Bytes to Long Words
   --
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Convert is new Ada.Unchecked_Conversion
     (Source => ByteArray32_t,
      Target => LongWordArray8_t);

   ---------------------------------------------
   --  Description:
   --    Conversion from Bytes to Long Long Words
   --
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Convert is new Ada.Unchecked_Conversion
     (Source => ByteArray32_t,
      Target => LongLongWordArray4_t);

   ---------------------------------------------
   --  Description:
   --    Conversion from Words to Bytes
   --
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Convert is new Ada.Unchecked_Conversion
     (Source => WordArray16_t,
      Target => ByteArray32_t);

   ---------------------------------------------
   --  Description:
   --    Conversion from Long Words (32-bit) to Bytes
   --
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Convert is new Ada.Unchecked_Conversion
     (Source => LongWordArray8_t,
      Target => ByteArray32_t);

   ---------------------------------------------
   --  Description:
   --    Conversion from Long Long Words (64-bit) to Bytes
   --
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Convert is new Ada.Unchecked_Conversion
     (Source => LongLongWordArray4_t,
      Target => ByteArray32_t);

   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256 (Data : ByteArray32_t) return Uint256_t
   is
      Uint256Local : Uint256_t;
   begin
      Uint256Local.Data := Data;
      return Uint256Local;
   end Uint256;

   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256 (Data : WordArray16_t) return Uint256_t
   is
      Uint256Local : Uint256_t;
   begin
      Uint256Local.Data := Convert (Data);
      return Uint256Local;
   end Uint256;

   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256 (Data : LongWordArray8_t) return Uint256_t
   is
      Uint256Local : Uint256_t;
   begin
      Uint256Local.Data := Convert (Data);
      return Uint256Local;
   end Uint256;


   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256Sprint (Data : LongWordArray8_t) return Uint256_t
   is
      DataLocal : LongWordArray8_t := Data;
      Uint256Local : Uint256_t;

      function ByteReorder (Input : CommonTypes.LongWord_t) return LongWord_t is
         BytesIn : LongWordArray_t (0 .. 3);
      begin
         BytesIn (0) := Input rem 256;
         BytesIn (1) := (Input / (256**1)) rem 256;
         BytesIn (2) := (Input / (256**2)) rem 256;
         BytesIn (3) := (Input / (256**3)) rem 256;

         return
           BytesIn (0) * (256 **3) +
           BytesIn (1) * (256 **2) +
           BytesIn (2) * (256 **1) +
           BytesIn (3);
--           return
--             BytesIn (3) * (256 **3) +
--             BytesIn (2) * (256 **2) +
--             BytesIn (1) * (256 **1) +
--             BytesIn (0);

      end ByteReorder;

   begin
      for i in LongWordArray8_t'Range loop
         DataLocal (i) := ByteReorder (Input => DataLocal (i));
      end loop;

      Uint256Local.Data := Convert (DataLocal);
      return Uint256Local;
   end Uint256Sprint;


   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256 (Data : LongLongWordArray4_t) return Uint256_t
   is
      Uint256Local : Uint256_t;
   begin
      Uint256Local.Data := Convert (Data);
      return Uint256Local;
   end Uint256;

   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256AsBytes (Uint256Local : Uint256_t) return ByteArray32_t
   is (Uint256Local.Data);

   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256AsWords (Uint256Local : Uint256_t) return WordArray16_t
   is (Convert (Uint256Local.Data));

   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256AsLongWords (Uint256Local : Uint256_t) return LongWordArray8_t
   is (Convert (Uint256Local.Data));

   ---------------------------------------------
   --  Implementation Notes:
   --    None.
   ---------------------------------------------
   function Uint256AsLongLongWords (Uint256Local : Uint256_t)
                                    return LongLongWordArray4_t
   is (Convert (Uint256Local.Data));

   ---------------------------------------------
   --  Implementation Notes :
   --    Makes use of a local function to convert Hexadecimal to Decimal. This
   --    function will only be called when casting N from a String to a number,
   --    therefore there is no defensive code to catch characters outside of
   --    the Hexadecimal (0-F) range.
   --
   --  # LOC estimate: xx #
   ---------------------------------------------
   function Uint256 (Input : String) return Uint256_t
   is
      BlockCounter : Integer := 0;
      Result : Uint256_t := NULLUint256;
      TempArray : LongLongWordArray4_t := NULLLongLongWordArray4;

      ---------------------------------------------
      --  Description :
      --    Local function to convert Hexadecimal to Decimal.
      --
      --  Implementation Notes:
      --    None.
      --
      --  # LOC estimate: 10 #
      ---------------------------------------------
      function HexCharToDec (Y : Character) return LongLongWord_t
      is
         ResultHex : LongLongWord_t := 0;
      begin

         if (Y >= 'A') and then (Y <= 'F') then
            ResultHex := LongLongWord_t (
              (Character'Pos (Y) - Character'Pos ('A')) + 10);
         else
            ResultHex := LongLongWord_t (
              Character'Pos (Y) - Character'Pos ('0'));
         end if;

         return ResultHex;
      end HexCharToDec;

   begin
      for I in Input'Range loop

         TempArray (LongLongWordArray4_t'Last - BlockCounter) := (
                 (TempArray (LongLongWordArray4_t'Last - BlockCounter)) * 16) +
                    HexCharToDec (Input (I));

         if (I /= Input'Last) and then (I mod 16 = 0) then
            BlockCounter := BlockCounter + 1;
         end if;

      end loop;

      Result.Data := Convert (TempArray);

      return Result;

   end Uint256;

end CommonTypes;
