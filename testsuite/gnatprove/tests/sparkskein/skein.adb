-------------------------------------------------------------------------------
-- (C) Altran UK Limited
--=============================================================================

-------------------------------------------------------------------------------
--                                                                           --
-- SPARK.Crypto.Hash.Skein                                                   --
--                                                                           --
-- Implementation Notes                                                      --
--                                                                           --
-- Originally based on the C reference implementation supplied by the Skein  --
-- design team. Performance is very close or better than that of the C code  --
-- at all optimization levels used. See www.skein-hash.info                  --
-------------------------------------------------------------------------------

with Ada.Unchecked_Conversion;

with System;                   use System;
with GNAT.Byte_Swapping;

package body Skein is

   function To_LittleEndian
     (W : in Interfaces.Unsigned_64)
      return Interfaces.Unsigned_64;
   --  pragma Inline (To_LittleEndian);

   function To_LittleEndian
     (W : in Interfaces.Unsigned_64)
      return Interfaces.Unsigned_64
   is
      function LSwap is
        new GNAT.Byte_Swapping.Swapped8 (Interfaces.Unsigned_64);
      --  pragma Inline (LSwap);
   begin
      if System.Default_Bit_Order = System.Low_Order_First then
         return W;
      else
         return LSwap (W);
      end if;
   end To_LittleEndian;

   -- Identifiers can't start with a digit in SPARK, so...
   -- type Bit_Size is (S256, S512, S1024);

   -- Number of rounds for the different block sizes
   Skein_512_Rounds_Total : constant := 72;

   -- Skein_512 round rotation constants
   subtype Rotation_Count is Natural range 2 .. 60;

   -- These constants are the values from the revised
   -- version 1.2 Skein Specification,
   --
   -- The values from the earlier version 1.1 of the spec
   -- follow each declaration as a comment.
   R_512_0_0 : constant Rotation_Count := 46; -- 38;
   R_512_0_1 : constant Rotation_Count := 36; -- 30;
   R_512_0_2 : constant Rotation_Count := 19; -- 50;
   R_512_0_3 : constant Rotation_Count := 37; -- 53;
   R_512_1_0 : constant Rotation_Count := 33; -- 48;
   R_512_1_1 : constant Rotation_Count := 27; -- 20;
   R_512_1_2 : constant Rotation_Count := 14; -- 43;
   R_512_1_3 : constant Rotation_Count := 42; -- 31;
   R_512_2_0 : constant Rotation_Count := 17; -- 34;
   R_512_2_1 : constant Rotation_Count := 49; -- 14;
   R_512_2_2 : constant Rotation_Count := 36; -- 15;
   R_512_2_3 : constant Rotation_Count := 39; -- 27;
   R_512_3_0 : constant Rotation_Count := 44; -- 26;
   R_512_3_1 : constant Rotation_Count :=  9; -- 12;
   R_512_3_2 : constant Rotation_Count := 54; -- 58;
   R_512_3_3 : constant Rotation_Count := 56; --  7;
   R_512_4_0 : constant Rotation_Count := 39; -- 33;
   R_512_4_1 : constant Rotation_Count := 30; -- 49;
   R_512_4_2 : constant Rotation_Count := 34; --  8;
   R_512_4_3 : constant Rotation_Count := 24; -- 42;
   R_512_5_0 : constant Rotation_Count := 13; -- 39;
   R_512_5_1 : constant Rotation_Count := 50; -- 27;
   R_512_5_2 : constant Rotation_Count := 10; -- 41;
   R_512_5_3 : constant Rotation_Count := 17; -- 14;
   R_512_6_0 : constant Rotation_Count := 25; -- 29;
   R_512_6_1 : constant Rotation_Count := 29; -- 26;
   R_512_6_2 : constant Rotation_Count := 39; -- 11;
   R_512_6_3 : constant Rotation_Count := 43; --  9;
   R_512_7_0 : constant Rotation_Count :=  8; -- 33;
   R_512_7_1 : constant Rotation_Count := 35; -- 51;
   R_512_7_2 : constant Rotation_Count := 56; -- 39;
   R_512_7_3 : constant Rotation_Count := 22; -- 35;

   Skein_Version      : constant := 1;
   Skein_ID_String_LE : constant Interfaces.Unsigned_32 := 16#33414853#; -- "SHA3" (little endian)

   Skein_Schema_Ver   : constant Interfaces.Unsigned_64 := (Interfaces.Unsigned_64 (Skein_Version) * 2**32) +
                                            Interfaces.Unsigned_64 (Skein_ID_String_LE);

   -- Revised Key Schedule Parity constant "C240" from version 1.3
   -- of the Skein specification.
   Skein_KS_Parity    : constant Interfaces.Unsigned_64 := 16#1BD11BDA_A9FC1A22#;

   Skein_Cfg_Tree_Info_Sequential : constant := 0;

   Skein_Cfg_Str_Len : constant := 4*8;

   procedure Put_64_LSB_First (Dst        : in out Byte_Seq;
                               Dst_Offset : in     Natural;
                               Src        : in     U64_Seq;
                               Byte_Count : in     Natural)
   --# derives Dst from Dst, Dst_Offset, Src, Byte_Count;
   --# pre Dst'First = 0 and
   --#     Src'First = 0 and
   --#     Dst'Last >= Dst_Offset + (Byte_Count - 1) and
   --#     Byte_Count <= (Src'Last + 1) * 8;
   is
   begin
      pragma Assert (Dst'First = 0,
                     "Put_64_LSB_First - Dst'First is not zero");
      pragma Assert (Src'First = 0,
                     "Put_64_LSB_First - Src'First is not zero");
      pragma Assert (Dst'Last >= Dst_Offset + (Byte_Count - 1),
                     "Put_64_LSB_First - Not enough room in Dst");
      pragma Assert ((Src'Last + 1) * 8 >= Byte_Count,
                     "Put_64_LSB_First - Not enough bytes in Src for Byte_Count");

      if Byte_Count >= 1 then
         for N in Natural range 0 .. (Byte_Count - 1) loop
            --# assert Byte_Count >= 1 and
            --#        N >= 0 and
            --#        N <= Byte_Count - 1 and
            --#        N < Byte_Count and
            --#        Byte_Count <= (Src'Last + 1) * 8 and
            --#        N < (Src'Last + 1) * 8 and
            --#        N <= (Src'Last * 8) + 7;

            --# check  N / 8 >= 0 and
            --#        N / 8 <= Src'Last;
            Dst (Dst_Offset + N) :=
              Interfaces.Unsigned_8 (Interfaces.Shift_Right
                                       (Src (N / 8),
                                        8 * (N mod 8)) and 16#FF#);
         end loop;
      end if;
   end Put_64_LSB_First;
   --  pragma Inline (Put_64_LSB_First);


   -- This version is fully portable (big-endian or little-endian), but slow
   procedure Get_64_LSB_First (Dst        :    out U64_Seq;
                               Src        : in     Byte_Seq;
                               Src_Offset : in     Natural)
   --# derives Dst from Src, Src_Offset;
   --# pre Src'First = 0 and
   --#     Dst'First = 0 and
   --#     Src_Offset <= Src'Last and
   --#     Src_Offset + (Dst'Last * 8) + 7 >= Src'First and
   --#     Src_Offset + (Dst'Last * 8) + 7 <= Src'Last and
   --#     Src_Offset + 7 <= Src'Last and
   --#     Src_Offset + Dst'Last * 8 <= Natural'Last;
   --# post for all I in Natural range Dst'First .. Dst'Last => (Dst (I) in Interfaces.Unsigned_64);
   is
      Dst_Index : Word_Count_T;
      Src_Index : Natural;
   begin
      pragma Assert (Src'First = 0,
                     "Get_64_LSB_First - Src'First is not zero");
      pragma Assert (Dst'First = 0,
                     "Get_64_LSB_First - Dst'First is not zero");
      pragma Assert (Src_Offset <= Src'Last,
                     "Get_64_LSB_First - Src_Offset is larger than Src'Last");
      pragma Assert (Src_Offset + (Dst'Last * 8) + 7 <= Src'Last,
                     "Get_64_LSB_First - Not enough bytes in Src for given Offset and Word_Count");

      Dst_Index := 0;
      Src_Index := Src_Offset;
      loop
         --# check Src_Index     in Src'Range and
         --#       Src_Index + 1 in Src'Range and
         --#       Src_Index + 2 in Src'Range and
         --#       Src_Index + 3 in Src'Range and
         --#       Src_Index + 4 in Src'Range and
         --#       Src_Index + 5 in Src'Range and
         --#       Src_Index + 6 in Src'Range and
         --#       Src_Index + 7 in Src'Range;

         --# accept F, 23, Dst, "OK";
         Dst (Dst_Index) :=
           Interfaces.Unsigned_64 (Src (Src_Index)) +
           Interfaces.Shift_Left (Interfaces.Unsigned_64 (Src (Src_Index + 1)), 8) +
           Interfaces.Shift_Left (Interfaces.Unsigned_64 (Src (Src_Index + 2)), 16) +
           Interfaces.Shift_Left (Interfaces.Unsigned_64 (Src (Src_Index + 3)), 24) +
           Interfaces.Shift_Left (Interfaces.Unsigned_64 (Src (Src_Index + 4)), 32) +
           Interfaces.Shift_Left (Interfaces.Unsigned_64 (Src (Src_Index + 5)), 40) +
           Interfaces.Shift_Left (Interfaces.Unsigned_64 (Src (Src_Index + 6)), 48) +
           Interfaces.Shift_Left (Interfaces.Unsigned_64 (Src (Src_Index + 7)), 56);
         --# end accept;

         --# assert (for all I in Natural range Dst'First .. Dst_Index => (Dst (I) in Interfaces.Unsigned_64)) and
         --#        Dst_Index in Dst'Range and
         --#        Dst'Last <= Word_Count_T'Last and
         --#        Src_Index = Src_Offset + (Dst_Index * 8) and
         --#        Src_Index >= Src_Offset and
         --#        Src_Index <= Src_Offset + (Dst'Last * 8) and
         --#        (Dst_Index /= Dst'Last -> (Dst_Index + 1 <= Natural'Last)) and
         --#        (Dst_Index /= Dst'Last -> (Src_Index + 8 <= Natural'Last));

         exit when Dst_Index = Dst'Last;

         --# check Dst_Index + 1 <= Natural'Last;
         Dst_Index := Dst_Index + 1;

         --# check Src_Index + 8 <= Natural'Last;
         Src_Index := Src_Index + 8;
      end loop;
      --# accept F, 602, Dst, Dst, "OK";
   end Get_64_LSB_First;
   --  pragma Inline (Get_64_LSB_First);

   procedure Skein_Start_New_Type (Field_Type  : in     U6;
                                   First_Block : in     Boolean;
                                   Final_Block : in     Boolean;
                                   Ctx         : in out Context_Header)
   --# derives Ctx from *, Field_Type, First_Block, Final_Block;
   --# post Ctx = Ctx~[Tweak_Words => Tweak_Value'(Byte_Count_LSB => 0,
   --#                                             Byte_Count_MSB => 0,
   --#                                             Reserved       => 0,
   --#                                             Tree_Level     => 0,
   --#                                             Bit_Pad        => False,
   --#                                             Field_Type     => Field_Type,
   --#                                             First_Block    => First_Block,
   --#                                             Final_Block    => Final_Block);
   --#                 Byte_Count => 0] and
   --#      Ctx.Hash_Bit_Len = Ctx~.Hash_Bit_Len and
   --#      Ctx.Byte_Count = 0;
   is
   begin
      Ctx.Tweak_Words := Tweak_Value'(Byte_Count_LSB => 0,
                                      Byte_Count_MSB => 0,
                                      Reserved       => 0,
                                      Tree_Level     => 0,
                                      Bit_Pad        => False,
                                      Field_Type     => Field_Type,
                                      First_Block    => First_Block,
                                      Final_Block    => Final_Block);
      Ctx.Byte_Count := 0;
   end Skein_Start_New_Type;

   procedure Skein_512_Process_Block
     (Ctx             : in out Skein_512_Context;
      Block           : in     Byte_Seq;
      Starting_Offset : in     Natural;
      Block_Count     : in     Positive_Block_512_Count_T;
      Byte_Count_Add  : in     Natural)
   --# derives Ctx from Ctx, Block, Starting_Offset, Block_Count, Byte_Count_Add;
   --# pre Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
   --#     Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count and
   --#     Block'First = 0 and
   --#     Starting_Offset + ((Block_Count - 1) * Skein_512_Block_Bytes_C) + 63 <= Block'Last and
   --#     Starting_Offset + 63 <= Block'Last and
   --#     Block'Last <= Natural'Last and
   --#     Starting_Offset <= Natural'Last - 63;
   --# post Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
   --#      Ctx.H.Hash_Bit_Len = Ctx~.H.Hash_Bit_Len and
   --#      Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count and
   --#      Ctx.H.Byte_Count   = Ctx~.H.Byte_Count;
   is
      WCNT : constant := Skein_512_State_Words_C;

      TS   : U64_Seq_3; -- Key schedule: tweak
      KS   : U64_Seq_9; -- Key schedule: chaining vars
      X    : U64_Seq_8; -- Local copy of vars
      W    : U64_Seq_8; -- Local copy of input block
      J    : Positive_Block_512_Count_T; -- loop counter

      Src_Offset : Natural;

      procedure Inject_Key (R : in Interfaces.Unsigned_64)
      with Global => (Input => (KS, TS),
                      In_Out => X)
      --# global in     KS;
      --#        in     TS;
      --#        in out X;
      --# derives X    from X, R, KS, TS;
      is
         subtype Injection_Range is Natural range 0 .. (WCNT - 1);
         KS_Modulus : constant Interfaces.Unsigned_64 := WCNT + 1;
      begin
         for I in Injection_Range loop
            X (I) := X (I) + KS (Natural ((R + Interfaces.Unsigned_64 (I)) mod KS_Modulus));
         end loop;

         X (WCNT - 3) := X (WCNT - 3) + TS (Natural (R mod 3));
         X (WCNT - 2) := X (WCNT - 2) + TS (Natural ((R + 1) mod 3));
         X (WCNT - 1) := X (WCNT - 1) + R; -- Avoid slide attacks
      end Inject_Key;
      --  pragma Inline (Inject_Key);

      procedure Round_1
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (0) := X (0) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_0_0);
         X (1) := X (1) xor X (0);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (2) := X (2) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_0_1);
         X (3) := X (3) xor X (2);

         --# assert True;

         X (4) := X (4) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_0_2);
         X (5) := X (5) xor X (4);

         --# assert True;

         X (6) := X (6) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_0_3);
         X (7) := X (7) xor X (6);
      end Round_1;
      --  pragma Inline (Round_1);

      procedure Round_2
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (2) := X (2) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_1_0);
         X (1) := X (1) xor X (2);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (4) := X (4) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_1_1);
         X (7) := X (7) xor X (4);

         --# assert True;

         X (6) := X (6) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_1_2);
         X (5) := X (5) xor X (6);

         --# assert True;

         X (0) := X (0) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_1_3);
         X (3) := X (3) xor X (0);
      end Round_2;
      --  pragma Inline (Round_2);


      procedure Round_3
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (4) := X (4) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_2_0);
         X (1) := X (1) xor X (4);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (6) := X (6) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_2_1);
         X (3) := X (3) xor X (6);

         --# assert True;

         X (0) := X (0) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_2_2);
         X (5) := X (5) xor X (0);

         --# assert True;

         X (2) := X (2) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_2_3);
         X (7) := X (7) xor X (2);
      end Round_3;
      --  pragma Inline (Round_3);

      procedure Round_4
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (6) := X (6) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_3_0);
         X (1) := X (1) xor X (6);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (0) := X (0) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_3_1);
         X (7) := X (7) xor X (0);

         --# assert True;

         X (2) := X (2) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_3_2);
         X (5) := X (5) xor X (2);

         --# assert True;

         X (4) := X (4) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_3_3);
         X (3) := X (3) xor X (4);
      end Round_4;
      --  pragma Inline (Round_4);

      procedure Round_5
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (0) := X (0) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_4_0);
         X (1) := X (1) xor X (0);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (2) := X (2) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_4_1);
         X (3) := X (3) xor X (2);

         --# assert True;

         X (4) := X (4) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_4_2);
         X (5) := X (5) xor X (4);

         --# assert True;

         X (6) := X (6) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_4_3);
         X (7) := X (7) xor X (6);
      end Round_5;
      --  pragma Inline (Round_5);

      procedure Round_6
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (2) := X (2) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_5_0);
         X (1) := X (1) xor X (2);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (4) := X (4) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_5_1);
         X (7) := X (7) xor X (4);

         --# assert True;

         X (6) := X (6) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_5_2);
         X (5) := X (5) xor X (6);

         --# assert True;

         X (0) := X (0) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_5_3);
         X (3) := X (3) xor X (0);
      end Round_6;
      --  pragma Inline (Round_6);

      procedure Round_7
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (4) := X (4) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_6_0);
         X (1) := X (1) xor X (4);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (6) := X (6) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_6_1);
         X (3) := X (3) xor X (6);

         --# assert True;

         X (0) := X (0) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_6_2);
         X (5) := X (5) xor X (0);

         --# assert True;

         X (2) := X (2) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_6_3);
         X (7) := X (7) xor X (2);
      end Round_7;
      --  pragma Inline (Round_7);

      procedure Round_8
      --# global in out X;
      --# derives X from X;
      is
      begin
         X (6) := X (6) + X (1);
         X (1) := Interfaces.Rotate_Left (X (1), R_512_7_0);
         X (1) := X (1) xor X (6);

         --  Extra cuts here to avoid VCG complexity explosion.
         --# assert True;

         X (0) := X (0) + X (7);
         X (7) := Interfaces.Rotate_Left (X (7), R_512_7_1);
         X (7) := X (7) xor X (0);

         --# assert True;

         X (2) := X (2) + X (5);
         X (5) := Interfaces.Rotate_Left (X (5), R_512_7_2);
         X (5) := X (5) xor X (2);

         --# assert True;

         X (4) := X (4) + X (3);
         X (3) := Interfaces.Rotate_Left (X (3), R_512_7_3);
         X (3) := X (3) xor X (4);
      end Round_8;
      --  pragma Inline (Round_8);

      procedure Initialize_Key_Schedule
        --  with Global => (Input => Ctx,
        --  Output => KS)
      --# global in     Ctx;
      --#           out KS;
      --# derives KS from Ctx;
      is
      begin
         -- For speed, we avoid a complete aggregate assignemnt to KS here.
         -- This generates a false-alarm from the flow-analyser, but this is
         -- OK, since type-safety is later re-established by the proof system.

         --# accept F, 23, KS, "Initialization here is total";
         KS (WCNT) := Skein_KS_Parity;

         for I in I8 loop
            KS (I)    := Ctx.X (I);
            KS (WCNT) := KS (WCNT) xor Ctx.X (I); -- Compute overall parity
            --# assert (for all J in I8 range I8'First .. I => (KS (J) in Interfaces.Unsigned_64)) and
            --#        KS (WCNT) in Interfaces.Unsigned_64;
         end loop;
         --# accept F, 602, KS, KS, "Initialization here is total";
      end Initialize_Key_Schedule;
      --  pragma Inline (Initialize_Key_Schedule);

      procedure Initialize_TS
        --  with Global => (Input => Ctx,
        --  Output => TS)
      --# global in     Ctx;
      --#           out TS;
      --# derives TS from Ctx;
      is
         W0 : Interfaces.Unsigned_64;
         W1 : Interfaces.Unsigned_64;

         function Tweak_To_Words
         --# return R => (for all I in Modifier_Words_Index => (R (I) in Interfaces.Unsigned_64));
         is new Ada.Unchecked_Conversion (Tweak_Value, Modifier_Words);
      begin
         --# accept W, 13, Tweak_To_Words, "Unchecked_Conversion here OK";
         W0 := Tweak_To_Words (Ctx.H.Tweak_Words)(0);
         W1 := Tweak_To_Words (Ctx.H.Tweak_Words)(1);
         --# end accept;
         TS := U64_Seq_3'(0 => W0,
                                 1 => W1,
                                 2 => W0 xor W1);
      end Initialize_TS;
      --  pragma Inline (Initialize_TS);

      procedure Do_First_Key_Injection
        with Global => (Input => (W, KS, TS),
                        Output => X)
      --# global in     W;
      --#        in     KS;
      --#        in     TS;
      --#           out X;
      --# derives X from W, KS, TS;
      is
      begin
         X := U64_Seq_8'(0 => W (0) + KS (0),
                                1 => W (1) + KS (1),
                                2 => W (2) + KS (2),
                                3 => W (3) + KS (3),
                                4 => W (4) + KS (4),
                                5 => W (5) + KS (5),
                                6 => W (6) + KS (6),
                                7 => W (7) + KS (7));
         X (WCNT - 3) := X (WCNT - 3) + TS (0);
         X (WCNT - 2) := X (WCNT - 2) + TS (1);
      end Do_First_Key_Injection;
      --  pragma Inline (Do_First_Key_Injection);

      procedure Threefish_Block
      --# global in     KS;
      --#        in     TS;
      --#        in out X;
      --# derives X    from X, KS, TS;
      is
      begin
         for R in Interfaces.Unsigned_64 range 1 .. (Skein_512_Rounds_Total / 8) loop
            Round_1;
            Round_2;
            Round_3;
            Round_4;
            Inject_Key (R * 2 - 1);
            Round_5;
            Round_6;
            Round_7;
            Round_8;
            Inject_Key (R * 2);
         end loop;
      end Threefish_Block;
      --  pragma Inline (Threefish_Block);

      procedure Update_Context
      --# global in out Ctx;
      --#        in     W;
      --#        in     X;
      --# derives Ctx from Ctx, W, X;
      --# post Ctx.H.Hash_Bit_Len = Ctx~.H.Hash_Bit_Len and
      --#      Ctx.H.Byte_Count   = Ctx~.H.Byte_Count;
      is
      begin
         Ctx.X := Skein_512_State_Words'(0 => X (0) xor W (0),
                                         1 => X (1) xor W (1),
                                         2 => X (2) xor W (2),
                                         3 => X (3) xor W (3),
                                         4 => X (4) xor W (4),
                                         5 => X (5) xor W (5),
                                         6 => X (6) xor W (6),
                                         7 => X (7) xor W (7));
      end Update_Context;
      --  pragma Inline (Update_Context);

   begin
      Src_Offset := Starting_Offset;
      J := 1;

      loop
         --# assert Ctx.H.Hash_Bit_Len = Ctx~.H.Hash_Bit_Len and
         --#        Ctx.H.Byte_Count   = Ctx~.H.Byte_Count and
         --#        J >= 1 and
         --#        J <= Block_Count and
         --#        Src_Offset = Starting_Offset + (J - 1) * Skein_512_Block_Bytes_C and
         --#        Src_Offset + 63 <= Block'Last and
         --#        Src_Offset + W'Last * 8 <= Natural'Last and
         --#        Starting_Offset + ((Block_Count - 1) * Skein_512_Block_Bytes_C) + 63 <= Block'Last and
         --#        Block'Last <= Natural'Last and
         --#        ((J < Block_Count) -> (Src_Offset + Skein_512_Block_Bytes_C <= Natural'Last));

         -- This implementation only supports 2**31 input bytes,
         -- so no carry over to Byte_Count_MSB here.
         Ctx.H.Tweak_Words.Byte_Count_LSB := Ctx.H.Tweak_Words.Byte_Count_LSB + Interfaces.Unsigned_64 (Byte_Count_Add);

         Initialize_Key_Schedule;

         Initialize_TS;

         Get_64_LSB_First (Dst        => W,
                           Src        => Block,
                           Src_Offset => Src_Offset);

         --# check for all I in I8 => (W (I) in Interfaces.Unsigned_64);

         -- Do the first full key injection
         Do_First_Key_Injection;

         Threefish_Block;

         -- Do the final "feedforward" xor, update context chaining vars
         Update_Context;

         Ctx.H.Tweak_Words.First_Block := False;

         exit when J >= Block_Count;

         J := J + 1;
         Src_Offset := Src_Offset + Skein_512_Block_Bytes_C;
      end loop;
   end Skein_512_Process_Block;


   procedure Skein_512_Init (Ctx        :    out Skein_512_Context;
                             HashBitLen : in     Initialized_Hash_Bit_Length)
   --# post Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
   --#      Ctx.H.Hash_Bit_Len = HashBitLen and
   --#      Ctx.H.Byte_Count = 0 and
   --#      Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count;
   is
      Cfg : Skein_512_State_Words;

      function Skein_512_State_Words_To_Bytes is new
        Ada.Unchecked_Conversion (Skein_512_State_Words, Skein_512_State_Bytes);
   begin
      -- Build/Process config block for hashing
      Ctx := Null_Skein_512_Context;

      Ctx.H.Hash_Bit_Len := HashBitLen; -- output has byte count

      Skein_Start_New_Type (Skein_Block_Type_Cfg, True, True, Ctx.H);

      --# check Ctx.H.Hash_Bit_Len = HashBitLen;

      -- Set the schema version, hash result length, and tree info.
      -- All others words are 0
      Cfg := Skein_512_State_Words'(0 => To_LittleEndian (Skein_Schema_Ver),
                                    1 => To_LittleEndian (Interfaces.Unsigned_64 (HashBitLen)),
                                    2 => To_LittleEndian (Skein_Cfg_Tree_Info_Sequential),
                                    others => 0);

      -- Compute the initial chaining values from config block

      -- First, zero the chaining bytes
      Ctx.X := Skein_512_State_Words'(others => 0);


      --# check Ctx.H.Hash_Bit_Len = HashBitLen;

      --# accept W, 13, Skein_512_State_Words_To_Bytes, "Unchecked Conversion OK";
      Skein_512_Process_Block (Ctx             => Ctx,
                               Block           => Skein_512_State_Words_To_Bytes (Cfg),
                               Starting_Offset => 0,
                               Block_Count     => 1,
                               Byte_Count_Add  => Skein_Cfg_Str_Len);
      --# end accept;

      --# check Ctx.H.Hash_Bit_Len = HashBitLen;

      -- Set up to process the data message portion of the hash (default)
      Skein_Start_New_Type (Skein_Block_Type_Msg, True, False, Ctx.H);

   end Skein_512_Init;

   procedure Skein_512_Update (Ctx : in out Skein_512_Context;
                               Msg : in     Byte_Seq)
   --# pre Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
   --#     Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count and
   --#     Msg'First = 0 and
   --#     Msg'Last < Natural'Last and
   --#     Msg'Last + Skein_512_Block_Bytes_C + 1 <= Natural'Last;
   --# post Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
   --#      Ctx.H.Hash_Bit_Len = Ctx~.H.Hash_Bit_Len and
   --#      Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count;
   is
      Msg_Byte_Count     : Natural;
      N                  : Skein_512_Block_Bytes_Index;
      Block_Count        : Positive_Block_512_Count_T;
      Current_Msg_Offset : Natural;
      Bytes_Hashed       : Natural;
      Tmp_B              : Skein_512_Block_Bytes;

      procedure Copy_Msg_To_B (Msg_Offset : in Natural;
                               Num_Bytes  : in Natural)
      --  with Global => (Input => Msg,
      --  In_Out => Ctx)
      --# global in out Ctx;
      --#        in     Msg;
      --# derives Ctx from Ctx, Msg, Msg_Offset, Num_Bytes;
      --# pre Ctx.H.Hash_Bit_Len > 0 and
      --#     Msg'First = 0 and
      --#     Msg_Offset in Msg'Range and
      --#     (Msg_Offset + (Num_Bytes - 1)) <= Msg'Last and
      --#     (Ctx.H.Byte_Count + (Num_Bytes - 1)) <= Ctx.B'Last;
      --# post Ctx.H.Hash_Bit_Len > 0 and
      --#      Ctx.H.Hash_Bit_Len = Ctx~.H.Hash_Bit_Len and
      --#      Ctx.H.Byte_Count   = Ctx~.H.Byte_Count + Num_Bytes and
      --#      Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count;
      is
         Src       : Natural;
         Dst       : Skein_512_Block_Bytes_Index;
         Final_Dst : Skein_512_Block_Bytes_Index;
         Final_Src : Natural;
      begin
         if Num_Bytes > 0 then

            Src := Msg_Offset;

            Dst := Ctx.H.Byte_Count;

            Final_Dst := Dst + (Num_Bytes - 1);
            Final_Src := Src + (Num_Bytes - 1);

            loop
               Ctx.B (Dst) := Msg (Src);

               --# assert Ctx.H.Hash_Bit_Len > 0 and
               --#        Ctx.H.Hash_Bit_Len = Ctx~.H.Hash_Bit_Len and
               --#        Ctx.H.Byte_Count = Ctx~.H.Byte_Count and
               --#        Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count and
               --#        (Ctx.H.Byte_Count + Num_Bytes) - 1 <= Ctx.B'Last and
               --#        Final_Src <= Msg'Last;
               exit when Dst >= Final_Dst or Src >= Final_Src;

               Dst := Dst + 1;
               Src := Src + 1;
            end loop;

            Ctx.H.Byte_Count := Ctx.H.Byte_Count + Num_Bytes;
         end if;
      end Copy_Msg_To_B;

   begin
      Msg_Byte_Count     := Msg'Last + 1;
      Current_Msg_Offset := 0;

      if (Msg_Byte_Count + Ctx.H.Byte_Count > Skein_512_Block_Bytes_C) then
         if Ctx.H.Byte_Count > 0 then

            N := Skein_512_Block_Bytes_C - Ctx.H.Byte_Count; -- number of bytes free in Ctx.B

            --# check N < Msg_Byte_Count;

            --# check N <= Msg'Last + 1;
            Copy_Msg_To_B (Current_Msg_Offset, N);
            Msg_Byte_Count     := Msg_Byte_Count - N;
            Current_Msg_Offset := Current_Msg_Offset + N;

            --# check Ctx.H.Byte_Count = Skein_512_Block_Bytes_C;

            Tmp_B := Ctx.B;
            Skein_512_Process_Block (Ctx             => Ctx,
                                     Block           => Tmp_B,
                                     Starting_Offset => 0,
                                     Block_Count     => 1,
                                     Byte_Count_Add  => Skein_512_Block_Bytes_C);
            Ctx.H.Byte_Count := 0;
         end if;

         -- Now process any remaining full blocks, directly from input message data
         if Msg_Byte_Count > Skein_512_Block_Bytes_C then

            Block_Count := (Msg_Byte_Count - 1) / Skein_512_Block_Bytes_C; -- Number of full blocks to process

            Skein_512_Process_Block (Ctx             => Ctx,
                                     Block           => Msg,
                                     Starting_Offset => Current_Msg_Offset,
                                     Block_Count     => Block_Count,
                                     Byte_Count_Add  => Skein_512_Block_Bytes_C);

            Bytes_Hashed := Block_Count * Skein_512_Block_Bytes_C;

            --# check Bytes_Hashed < Msg_Byte_Count;
            Msg_Byte_Count     := Msg_Byte_Count     - Bytes_Hashed;

            Current_Msg_Offset := Current_Msg_Offset + Bytes_Hashed;
         end if;

      end if;

      -- Finally, there might be fewer than Skein_512_Block_Bytes_C bytes left
      -- over that are not yet hashed. Copy these to Ctx.B for processing
      -- in any subsequent call to _Update or _Final.
      Copy_Msg_To_B (Current_Msg_Offset, Msg_Byte_Count);

   end Skein_512_Update;

   procedure Skein_512_Final (Ctx    : in     Skein_512_Context;
                              Result :    out Byte_Seq)
   --# pre  Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
   --#      Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count and
   --#      Result'First = 0 and
   --#      (Ctx.H.Hash_Bit_Len + 7) / 8 <= Result'Last + 1;
   is
      subtype Output_Byte_Count_T  is Natural range 1 .. (Hash_Bit_Length'Last + 7) / 8;
      subtype Output_Block_Count_T is Natural range 0 .. (Output_Byte_Count_T'Last + 63) / Skein_512_Block_Bytes_C;
      subtype Positive_Output_Block_Count_T is Output_Block_Count_T range 1 .. Output_Block_Count_T'Last;

      Local_Ctx          : Skein_512_Context;
      N                  : Natural;
      Blocks_Done        : Output_Block_Count_T;
      Blocks_Required    : Positive_Output_Block_Count_T;
      Byte_Count         : Output_Byte_Count_T;
      X                  : Skein_512_State_Words;
      Tmp_B              : Skein_512_Block_Bytes;
      Tmp_Byte_Count_Add : Natural;

      procedure Zero_Pad_B
      --# global in out Local_Ctx;
      --# derives Local_Ctx from Local_Ctx;
      --# pre Local_Ctx.H.Byte_Count < Skein_512_Block_Bytes_C and
      --#     Local_Ctx.H.Hash_Bit_Len > 0;
      --# post Local_Ctx.H.Hash_Bit_Len = Local_Ctx~.H.Hash_Bit_Len and
      --#      Local_Ctx.H.Hash_Bit_Len > 0 and
      --#      Local_Ctx.H.Byte_Count < Skein_512_Block_Bytes_C and
      --#      Local_Ctx.H.Byte_Count = Local_Ctx~.H.Byte_Count;
      is
      begin
         for I in Skein_512_Block_Bytes_Index range Local_Ctx.H.Byte_Count .. Skein_512_Block_Bytes_Index'Last loop
            --# assert Local_Ctx.H.Hash_Bit_Len = Local_Ctx~.H.Hash_Bit_Len and
            --#        Local_Ctx.H.Hash_Bit_Len > 0 and
            --#        Local_Ctx.H.Byte_Count < Skein_512_Block_Bytes_C and
            --#        Local_Ctx.H.Byte_Count = Local_Ctx~.H.Byte_Count;
            Local_Ctx.B (I) := 0;
         end loop;
      end Zero_Pad_B;
      --  pragma Inline (Zero_Pad_B);

      procedure Set_B_Counter (Counter : in Interfaces.Unsigned_64)
      --# global in out Local_Ctx;
      --# derives Local_Ctx from Local_Ctx, Counter;
      --# pre Local_Ctx.H.Hash_Bit_Len > 0;
      --# post Local_Ctx.H.Hash_Bit_Len > 0;
      is
      begin
         Local_Ctx.B (0) := Interfaces.Unsigned_8 (Counter and 16#FF#);
         Local_Ctx.B (1) := Interfaces.Unsigned_8 (Interfaces.Shift_Right (Counter, 8)  and 16#FF#);
         Local_Ctx.B (2) := Interfaces.Unsigned_8 (Interfaces.Shift_Right (Counter, 16) and 16#FF#);
         Local_Ctx.B (3) := Interfaces.Unsigned_8 (Interfaces.Shift_Right (Counter, 24) and 16#FF#);
         Local_Ctx.B (4) := Interfaces.Unsigned_8 (Interfaces.Shift_Right (Counter, 32) and 16#FF#);
         Local_Ctx.B (5) := Interfaces.Unsigned_8 (Interfaces.Shift_Right (Counter, 40) and 16#FF#);
         Local_Ctx.B (6) := Interfaces.Unsigned_8 (Interfaces.Shift_Right (Counter, 48) and 16#FF#);
         Local_Ctx.B (7) := Interfaces.Unsigned_8 (Interfaces.Shift_Right (Counter, 56) and 16#FF#);
      end Set_B_Counter;
      --  pragma Inline (Set_B_Counter);

   begin
      Local_Ctx := Ctx;
      --# check Local_Ctx.H.Hash_Bit_Len > 0;
      Result := (others => 0);

      Local_Ctx.H.Tweak_Words.Final_Block := True; -- Tag as the final block
      if (Local_Ctx.H.Byte_Count < Skein_512_Block_Bytes_C) then
         Zero_Pad_B;
      end if;

      Tmp_B := Local_Ctx.B;
      Tmp_Byte_Count_Add := Local_Ctx.H.Byte_Count;

      Skein_512_Process_Block (Ctx             => Local_Ctx,
                               Block           => Tmp_B,
                               Starting_Offset => 0,
                               Block_Count     => 1,
                               Byte_Count_Add  => Tmp_Byte_Count_Add);

      -- Now output the result
      Byte_Count := (Local_Ctx.H.Hash_Bit_Len + 7) / 8; -- Total number of output bytes

      --# check Byte_Count <= Result'Last + 1;

      -- Run Threefish in "counter mode" to generate more output
      Local_Ctx.B := Skein_512_Block_Bytes'(others => 0); -- Zero out Local_Ctx.B, so it can hold the counter
      X := Local_Ctx.X; -- Keep a local copy of counter mode "key"

      Blocks_Required := (Byte_Count + 63) / 64;
      Blocks_Done := 0;

      loop
         --# assert Local_Ctx.H.Hash_Bit_Len > 0 and
         --#        Byte_Count <= Result'Last + 1 and
         --#        Blocks_Done * Skein_512_Block_Bytes_C < Byte_Count and
         --#        Blocks_Done * Skein_512_Block_Bytes_C < Result'Last + 1 and
         --#        Blocks_Done < Blocks_Required and
         --#        Blocks_Required = (Byte_Count + 63) / 64;

         Set_B_Counter (Interfaces.Unsigned_64 (Blocks_Done));

         Skein_Start_New_Type (Field_Type  => Skein_Block_Type_Out,
                               First_Block => True,
                               Final_Block => True,
                               Ctx         => Local_Ctx.H);


         -- Run "Counter Mode"
         Tmp_B := Local_Ctx.B;
         Skein_512_Process_Block (Ctx             => Local_Ctx,
                                  Block           => Tmp_B,
                                  Starting_Offset => 0,
                                  Block_Count     => 1,
                                  Byte_Count_Add  => 8);

         N := Byte_Count - (Blocks_Done * Skein_512_Block_Bytes_C); -- number of output bytes left to go
         if (N >= Skein_512_Block_Bytes_C) then
            N := Skein_512_Block_Bytes_C;
         end if;

         -- Push the output Local_Ctx.X into output buffer Hash
         Put_64_LSB_First (Dst          => Result,
                           Dst_Offset   => Blocks_Done * Skein_512_Block_Bytes_C,
                           Src          => Local_Ctx.X,
                           Byte_Count   => N);

         Local_Ctx.X := X; -- restore the counter mode key for next time

         Blocks_Done := Blocks_Done + 1;
         exit when Blocks_Done >= Blocks_Required;

      end loop;

   end Skein_512_Final;


   function Skein_512_Hash (Data : in Byte_Seq) return Skein_512_State_Bytes
   is
      Ctx    : Skein_512_Context;
      Result : Skein_512_State_Bytes;
   begin
      Skein_512_Init (Ctx        => Ctx,
                      HashBitLen => 512);

      Skein_512_Update (Ctx => Ctx,
                        Msg => Data);

      Skein_512_Final (Ctx    => Ctx,
                       Result => Result);
      return Result;
   end Skein_512_Hash;

end Skein;
