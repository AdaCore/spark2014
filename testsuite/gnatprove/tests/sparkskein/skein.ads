-------------------------------------------------------------------------------
-- (C) Altran UK Limited
--=============================================================================

-------------------------------------------------------------------------------
--                                                                           --
-- SPARK.Crypto.Hash.Skein                                                   --
--                                                                           --
-- Description                                                               --
--                                                                           --
-- Skein hash function. Derived from the SPARKSkein release originally       --
-- appearing on www.skein-hash.info                                          --
--                                                                           --
-- Currently, this package only implements the main Skein hash function      --
-- with a 512-bit block size                                                 --
--                                                                           --
-- Language                                                                  --
--   Specification : SPARK                                                   --
--   Private Part  : SPARK                                                   --
--   Body          : SPARK                                                   --
--                                                                           --
-- Runtime Requirements and Dependencies                                     --
--   None                                                                    --
--                                                                           --
-- Verification                                                              --
--   Full proof of type-safety with Simplifer and Victor. Clients must       --
-- respect the stated preconditions.                                         --
--                                                                           --
-- Exceptions                                                                --
--   None                                                                    --
-------------------------------------------------------------------------------

with Interfaces;
with System;

use type Interfaces.Unsigned_64;

--# inherit Ada.Unchecked_Conversion,
--#         SPARK,
--#         SPARK.Crypto,
--#         SPARK.Unsigned,
--#         SPARK.Crypto.Hash,
--#         System;

package Skein is

   subtype I3   is Natural range 0 .. 2;
   subtype I4   is Natural range 0 .. 3;
   subtype I6   is Natural range 0 .. 5;
   subtype I7   is Natural range 0 .. 6;
   subtype I8   is Natural range 0 .. 7;
   subtype I9   is Natural range 0 .. 8;
   subtype I16  is Natural range 0 .. 15;
   subtype I64  is Natural range 0 .. 63;
   subtype I128 is Natural range 0 .. 127;

   type Byte_Seq is array (Natural range <>) of Interfaces.Unsigned_8;
   for Byte_Seq'Alignment use 8;

   subtype Byte_Seq_4   is Byte_Seq (I4);
   subtype Byte_Seq_8   is Byte_Seq (I8);
   subtype Byte_Seq_16  is Byte_Seq (I16);
   subtype Byte_Seq_64  is Byte_Seq (I64);
   subtype Byte_Seq_128 is Byte_Seq (I128);

   -- 2**N bytes is 2**(N-3) 64-bit words
   subtype Word_Count_T is Natural range 0 .. ((Natural'Last + 1) / 8 - 1);
   subtype Positive_Word_Count_T is Natural range 1 .. Word_Count_T'Last;

   type U64_Seq is array (Word_Count_T range <>) of Interfaces.Unsigned_64;
   for U64_Seq'Alignment use 8;

   subtype U64_Seq_3  is U64_Seq (I3);
   subtype U64_Seq_4  is U64_Seq (I4);
   subtype U64_Seq_8  is U64_Seq (I8);
   subtype U64_Seq_9  is U64_Seq (I9);
   subtype U64_Seq_16 is U64_Seq (I16);

   -- We limit the length of the output hash to U64'Last - 7 to
   -- avoid overflow in the calculation of the number of bytes needed
   -- in Skein_512_Final. This is an undocumented limitation of reference
   -- implementation in C.  The value 0 is used to indicate a context
   -- that has not yet been initialized.
   subtype Hash_Bit_Length is Natural range 0 .. Natural'Last - 7;

   subtype Initialized_Hash_Bit_Length is
     Hash_Bit_Length range 1 .. Hash_Bit_Length'Last;

   -------------------------------------------------------------------
   -- Constants and types specific to Skein_512
   -------------------------------------------------------------------

   Skein_512_State_Words_C : constant :=  8;
   Skein_512_State_Bytes_C : constant :=  8 * Skein_512_State_Words_C;

   Skein_512_State_Bits_C  : constant := 64 * Skein_512_State_Words_C;
   Skein_512_Block_Bytes_C : constant :=  8 * Skein_512_State_Words_C;

   subtype Skein_512_State_Words_Index is Natural range 0 .. (Skein_512_State_Words_C - 1);
   subtype Skein_512_State_Words is U64_Seq (Skein_512_State_Words_Index);

   subtype Skein_512_Block_Bytes_Count is Natural range 0 .. Skein_512_Block_Bytes_C;
   subtype Skein_512_Block_Bytes_Index is Natural range 0 .. (Skein_512_Block_Bytes_C - 1);
   subtype Skein_512_Block_Bytes is Byte_Seq (Skein_512_Block_Bytes_Index);

   subtype Skein_512_State_Bytes_Index is Natural range 0 .. (Skein_512_State_Bytes_C - 1);
   subtype Skein_512_State_Bytes is Byte_Seq (Skein_512_State_Bytes_Index);

   -- (Natural'Last + 1) bytes is (Natural'Last + 1) / 64 512-bit blocks
   subtype Block_512_Count_T is Natural range 0 .. ((Natural'Last + 1) / 64 - 1);
   subtype Positive_Block_512_Count_T is Natural range 1 .. Block_512_Count_T'Last;

   -- Make the context limited private to prevent assignment and comparison
   -- of contexts. These operations almost certainly don't make sense.
   type Skein_512_Context is limited private;

   -------------------------------------------------------------------
   -- Proof functions that yield properties of a Skein_512_Context
   -- These form a simple refinement relation between the private
   -- and full views of this type.  These are used below to specify
   -- particular pre- and post-conditions on a Context, but without
   -- having to make the entire type publically visible.
   -------------------------------------------------------------------

   --# function Hash_Bit_Len_Of (Ctx : in Skein_512_Context) return Hash_Bit_Length;

   --# function Byte_Count_Of   (Ctx : in Skein_512_Context) return Natural;


   -------------------------------------------------------------------
   -- Skein 512 Exported Operations
   -------------------------------------------------------------------

   procedure Skein_512_Init (Ctx        :    out Skein_512_Context;
                             HashBitLen : in     Initialized_Hash_Bit_Length);
   --# derives Ctx from HashBitLen;
   --# post Hash_Bit_Len_Of (Ctx) in Initialized_Hash_Bit_Length and
   --#      Hash_Bit_Len_Of (Ctx) = HashBitLen and
   --#      Byte_Count_Of (Ctx) = 0 and
   --#      Byte_Count_Of (Ctx) in Skein_512_Block_Bytes_Count;

   procedure Skein_512_Update (Ctx : in out Skein_512_Context;
                               Msg : in     Byte_Seq);
   --# derives Ctx from Ctx, Msg;
   --# pre Hash_Bit_Len_Of (Ctx) in Initialized_Hash_Bit_Length and
   --#     Byte_Count_Of (Ctx) in Skein_512_Block_Bytes_Count and
   --#     Msg'First = 0 and
   --#     Msg'Last < Natural'Last and
   --#     Msg'Last + Skein_512_Block_Bytes_C < Natural'Last;
   --# post Hash_Bit_Len_Of (Ctx) in Initialized_Hash_Bit_Length and
   --#      Hash_Bit_Len_Of (Ctx) = Hash_Bit_Len_Of (Ctx~) and
   --#      Byte_Count_Of (Ctx) in Skein_512_Block_Bytes_Count;

   procedure Skein_512_Final (Ctx    : in     Skein_512_Context;
                              Result :    out Byte_Seq);
   --# derives Result from Ctx;
   --# pre  Hash_Bit_Len_Of (Ctx) in Initialized_Hash_Bit_Length and
   --#      Byte_Count_Of (Ctx) in Skein_512_Block_Bytes_Count and
   --#      Result'First = 0 and
   --#      (Hash_Bit_Len_Of (Ctx) + 7) / 8 <= Result'Last + 1;

   -- Returns a 512-bit hash of Data using 512-bit block size.
   function Skein_512_Hash (Data : in Byte_Seq) return Skein_512_State_Bytes;
   --# pre Data'First = 0 and
   --#     Data'Last + Skein_512_Block_Bytes_C < Natural'Last;

private

   type U6 is mod 2**6;
   type U7 is mod 2**7;

   Skein_Max_State_Words_C : constant := 16;

   Skein_Modifier_Words_C  : constant :=  2; -- number of modifier (tweak) words
   subtype Modifier_Words_Index is Natural range 0 .. (Skein_Modifier_Words_C - 1);
   subtype Modifier_Words is U64_Seq (Modifier_Words_Index);

   -- Constant for values of Field_Type below.  Could use an
   -- enumeration type here with a non-standard representation, but
   -- this can be slow.
   Skein_Block_Type_Key   : constant U6 :=  0;  -- key, for MAC and KDF
   Skein_Block_Type_Cfg   : constant U6 :=  4;  -- configuration block
   Skein_Block_Type_Pers  : constant U6 :=  8;  -- personalization string
   Skein_Block_Type_PK    : constant U6 := 12;  -- public key (for digital signature hashing)
   Skein_Block_Type_KDF   : constant U6 := 16;  -- key identifier for KDF
   Skein_Block_Type_Nonce : constant U6 := 20;  -- nonce for PRNG
   Skein_Block_Type_Msg   : constant U6 := 48;  -- message processing
   Skein_Block_Type_Out   : constant U6 := 63;  -- output stage
   Skein_Block_Type_Mask  : constant U6 := 63;  -- bit field mask

   -- System_Default_Bit_Order (SDBO for short)
   -- Set up this constant so that
   -- 0 = Little-endian
   -- 1 = Big-endian
   SDBO : constant := 1 - System.Bit_Order'Pos (System.Default_Bit_Order);

   -- NOTE - in the declaration of three "one bit" fields here, it seem
   -- more natural to use Boolean than a modular integer types.  To meet
   -- the Skein spec, this relies on the fact that False is represented
   -- by the value 0, and True is represented by the value 1.
   --
   -- This behaviour is implied by AARM 13.4(8) and is known to be OK
   -- for all known implementations.
   type Tweak_Value is record
      Byte_Count_LSB : Interfaces.Unsigned_64;
      Byte_Count_MSB : Interfaces.Unsigned_32;
      Reserved       : Interfaces.Unsigned_16;
      Tree_Level     : U7;
      Bit_Pad        : Boolean;
      Field_Type     : U6;
      First_Block    : Boolean;
      Final_Block    : Boolean;
   end record;

   ----------------------------------------------------------------------------
   -- See Skein Specification, Table 5.
   --
   -- On a LITTLE ENDIAN machine, we lay out this record exactly as specified
   -- in Table 5 of the specification.
   --
   -- On a BIG ENDIAN machine, we swap the bytes of T1 (the second 64-bit word)
   -- around, so that when Unchecked_Converted to Modifier_Words, the second
   -- word has its MSB where expected.
   --
   -- For example, we expect Final_Block to be the most-significant bit, so
   -- this is furthest "up" away from the base of the record on a little-endian
   -- machine, at bit postition 127.
   --
   -- On a big-endian machine, we need to place Final_Block where the MSB
   -- will be _after_ conversion to words, so we place it "nearest" the base
   -- of the second word at bit postion 64.
   --
   -- SDBO has value 0 (little-endian) or 1 (big-endian), so we can use
   -- it apply the necessary adjustment to the bit positions below.
   ----------------------------------------------------------------------------
   for Tweak_Value use record
      Byte_Count_LSB at 0 range   0 ..  63;

      Byte_Count_MSB at 0 range  64 + (SDBO * 32) ..  64 + (SDBO * 32) + 31; -- 32 bits
      Reserved       at 0 range  96 - (SDBO * 16) ..  96 - (SDBO * 16) + 15; -- 16 bits
      Tree_Level     at 0 range 112 - (SDBO * 39) .. 112 - (SDBO * 39) + 6;  --  7 bits
      Bit_Pad        at 0 range 119 - (SDBO * 47) .. 119 - (SDBO * 47) + 0;  --  1 bit
      Field_Type     at 0 range 120 - (SDBO * 54) .. 120 - (SDBO * 54) + 5;  --  6 bits
      First_Block    at 0 range 126 - (SDBO * 61) .. 126 - (SDBO * 61) + 0;  --  1 bit
      Final_Block    at 0 range 127 - (SDBO * 63) .. 127 - (SDBO * 63) + 0;  --  1 bit
   end record;
   for Tweak_Value'Size use 128;
   for Tweak_Value'Alignment use 8;

   Null_Tweak_Value : constant Tweak_Value :=
     Tweak_Value'(Byte_Count_LSB => 0,
                  Byte_Count_MSB => 0,
                  Reserved       => 0,
                  Tree_Level     => 0,
                  Bit_Pad        => False,
                  Field_Type     => 0,
                  First_Block    => False,
                  Final_Block    => False);


   -- Context header common to all block sizes
   type Context_Header is record
      Tweak_Words  : Tweak_Value;

      -- size of hash result, in bits.  0 = not yet initialized
      Hash_Bit_Len : Hash_Bit_Length;

      -- Current byte count in buffer - actual range depends on
      -- block size.
      --  In Skein_256,  Byte_Count is range 0 .. 32;
      --  In Skein_512,  Byte_Count is range 0 .. 64;
      --  In Skein_1024, Byte_Count is range 0 .. 128;
      --
      -- These constraints are asserted as preconditions
      -- on the specific _Init, _Update, and _Final
      -- procedures above for each block size.
      Byte_Count   : Natural;

   end record;

   Null_Context_Header : constant Context_Header :=
     Context_Header'(Hash_Bit_Len => 0,
                     Byte_Count   => 0,
                     Tweak_Words  => Null_Tweak_Value);

   -------------------------------------------------------------------
   -- Constants and types specific to Skein_512
   -------------------------------------------------------------------

   type Skein_512_Context is record -- 512-bit Skein hash context structure
      H : Context_Header;        -- common header context variables
      X : Skein_512_State_Words; -- chaining variables
      B : Skein_512_Block_Bytes; -- partial block buffer (8-byte aligned)
   end record;
   for Skein_512_Context'Alignment use 64;

   Null_Skein_512_Context : constant Skein_512_Context :=
     Skein_512_Context'(H => Null_Context_Header,
                        X => Skein_512_State_Words'(others => 0),
                        B => Skein_512_Block_Bytes'(others => 0));


end Skein;
