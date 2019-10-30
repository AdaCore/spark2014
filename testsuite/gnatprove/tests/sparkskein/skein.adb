------------------------------------------------------------------------------
-- (C) Altran Praxis Limited
------------------------------------------------------------------------------
--
-- SPARKSkein is free software; you can redistribute it and/or modify it
-- under terms of the GNU General Public License as published by the Free
-- Software Foundation; either version 3, or (at your option) any later
-- version. SPARKSkein is distributed in the hope that it will be
-- useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
-- Public License for more details. You should have received a copy of the GNU
-- General Public License distributed with SPARKSkein; see file
-- COPYING3. If not, go to http://www.gnu.org/licenses for a complete copy of
-- the license.
--
-- As a special exception, if other files instantiate generics from this unit,
-- or you link this unit with other files to produce an executable, this unit
-- does not by itself cause the resulting executable to be covered by the GNU
-- General Public License. This exception does not however invalidate any other
-- reasons why the executable file might be covered by the GNU Public License.
--
--==============================================================================

with Ada.Unchecked_Conversion;
with GNAT.Byte_Swapping;

package body Skein
   with SPARK_Mode => On
is
   use Interfaces;

   --  Number of rounds for the different block sizes
   Skein_512_Rounds_Total : constant := 72;

   WCNT_512 : constant := Skein_512_State_Words_C;

   --  Skein_512 round rotation constants
   subtype Rotation_Count is Natural range 2 .. 60;

   --  These constants are the values from the revised
   --  version 1.2 Skein Specification,
   --
   --  The values from the earlier version 1.1 of the spec
   --  follow each declaration as a comment.
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
   Skein_ID_String_LE : constant U32 := 16#33414853#; -- "SHA3" (little endian)

   Skein_Schema_Ver   : constant U64 := (U64 (Skein_Version) * 2**32) +
                                            U64 (Skein_ID_String_LE);

   --  Revised Key Schedule Parity constant "C240" from version 1.3
   --  of the Skein specification.
   Skein_KS_Parity    : constant U64 := 16#1BD11BDA_A9FC1A22#;

   Skein_Cfg_Tree_Info_Sequential : constant := 0;

   Skein_Cfg_Str_Len : constant := 4*8;

   --  Local packages
   package Trace
   is
      Skein_Rnd_Special     : constant := 1000;
      Skein_Rnd_Key_Initial : constant := Skein_Rnd_Special + 0;
      Skein_Rnd_Key_Inject  : constant := Skein_Rnd_Special + 1;
      Skein_Rnd_Feed_Fwd    : constant := Skein_Rnd_Special + 2;

      procedure Set_Flags (F : in Skein.Debug_Flag_Set)
        with Global  => null,
             Depends => (null => F);

      procedure Show_8 (S     : in Skein.Byte_Seq_Pred;
                        Count : in Skein.U64)
        with Global  => null,
             Depends => (null => (S, Count)),
             Pre     => Count <= S'Length;

      procedure Show_Msg_8 (Msg   : in String;
                            S     : in Skein.Byte_Seq_Pred;
                            Count : in Skein.U64)
        with Global  => null,
             Depends => (null => (Msg, S, Count)),
             Pre     => Count <= S'Length;

      procedure Show_64 (S     : in Skein.U64_Seq;
                         Count : in Skein.U64)
        with Global  => null,
             Depends => (null => (S, Count)),
             Pre     => Count <= S'Length;

      procedure Show_Msg_64 (Msg   : in String;
                             S     : in Skein.U64_Seq;
                             Count : in Skein.U64)
        with Global  => null,
             Depends => (null => (Msg, S, Count)),
             Pre     => Count <= S'Length;
      pragma Unreferenced (Show_Msg_64);

      procedure Show_Final
        (Bits         : in Skein.Bit_Size;
         H            : in Skein.Context_Header;
         Block        : in Skein.Byte_Seq_Pred;
         Byte_Count   : in Skein.U64;
         Block_Offset : in Skein.U64)
        with Global  => null,
             Depends => (null => (Bits, H, Block, Byte_Count, Block_Offset)),
             Pre     => Block'First = 0;

      procedure Show_Round
        (Bits : in Skein.Bit_Size;
         H    : in Skein.Context_Header;
         R    : in Skein.U64;
         X    : in Skein.U64_Seq)
        with Global  => null,
             Depends => (null => (Bits, H, R, X)),
             Pre     => X'First = 0;

      procedure Show_Block
        (Bits         : in Skein.Bit_Size;
         H            : in Skein.Context_Header;
         X            : in Skein.U64_Seq;
         Block        : in Skein.Byte_Seq_Pred;
         Block_Offset : in Skein.U64;
         W            : in Skein.U64_Seq;
         KS           : in Skein.U64_Seq;
         TS           : in Skein.U64_Seq)
        with Global  => null,
             Depends => (null => (Bits, H, X, Block, Block_Offset, W, KS, TS)),
             Pre     => X'First = 0 and
             Block'First = 0 and
             W'First = 0 and
             KS'First = 0 and
             TS'First = 0;

      procedure Show_Key
        (Bits      : in Skein.Bit_Size;
         H         : in Skein.Context_Header;
         Key_Bytes : in Skein.Byte_Seq_Pred)
        with Global  => null,
             Depends => (null => (Bits, H, Key_Bytes)),
             Pre     => Key_Bytes'First = 0;
      pragma Unreferenced (Show_Key);

   end Trace;


   --  Local instantiations
   function Tweak_To_Words is new Ada.Unchecked_Conversion
     (Tweak_Value, Modifier_Words);

   function Skein_512_State_Words_To_Bytes is new
     Ada.Unchecked_Conversion (Skein_512_State_Words, Skein_512_State_Bytes);


   --  Local package body stubs
   package body Trace is separate;


   --  Local subprogram bodies
   function To_LittleEndian (W : in Unsigned_64) return Unsigned_64
     with Global => null
   is
      function LSwap is new
        GNAT.Byte_Swapping.Swapped8 (Interfaces.Unsigned_64);

      use type System.Bit_Order;
   begin
      if System.Default_Bit_Order = System.Low_Order_First then
         return W;
      else
         return LSwap (W);
      end if;
   end To_LittleEndian;

   procedure Put_64_LSB_First (Dst        : in out Byte_Seq_Pred;
                               Dst_Offset : in     U64;
                               Src        : in     U64_Seq;
                               Byte_Count : in     U64)
--  UNCOMMENT TO VERIFY Put_64_LSB_First SEPARATELY
--       with Pre => Dst'First = 0 and
--                   Src'First = 0 and
--                   (Byte_Count = 0
--                      or
--                    Add_In_Range (Dst_Offset, Byte_Count - 1)) and
--                   Dst'Last >= Dst_Offset + (Byte_Count - 1) and
--                   Src'Last < U64'Last / 8 and
--                   Byte_Count <= (Src'Last + 1) * 8
   is
   begin
      if Byte_Count >= 1 then
         for N in U64 range 0 .. (Byte_Count - 1) loop
            Dst (Dst_Offset + N) :=
              Byte (Shift_Right
                      (Unsigned_64 (Src (N / 8)),
                       Natural (8 * (N and 7))) and 16#FF#);
         end loop;
      end if;
   end Put_64_LSB_First;

   --  This version is fully portable (big- or little-endian), but slow
   procedure Get_64_LSB_First (Dst        :    out U64_Seq;
                               Src        : in     Byte_Seq_Pred;
                               Src_Offset : in     U64)
--  UNCOMMENT TO VERIFY Get_64_LSB_First SEPARATELY
--       with Pre => Src'First = 0 and
--                   Dst'First = 0 and
--                   Src_Offset <= Src'Last and
--                   Dst'Last < U64'Last / 8 and
--                   Add_In_Range (Dst'Last * 8, 7) and
--                   Add_In_Range (Src_Offset, Dst'Last * 8 + 7) and
--                   Src_Offset + Dst'Last * 8 + 7 <= Src'Last
   is
   begin
      for Dst_Index in Dst'Range loop
         declare
            Src_Index : constant U64 := Src_Offset + Dst_Index * 8;
         begin
            Dst (Dst_Index) :=
              U64 (Src (Src_Index)) +
              Shift_Left (U64 (Src (Src_Index + 1)), 8) +
              Shift_Left (U64 (Src (Src_Index + 2)), 16) +
              Shift_Left (U64 (Src (Src_Index + 3)), 24) +
              Shift_Left (U64 (Src (Src_Index + 4)), 32) +
              Shift_Left (U64 (Src (Src_Index + 5)), 40) +
              Shift_Left (U64 (Src (Src_Index + 6)), 48) +
              Shift_Left (U64 (Src (Src_Index + 7)), 56);
         end;
      end loop;
   end Get_64_LSB_First;

   procedure Skein_Start_New_Type (Field_Type  : in     U6;
                                   First_Block : in     Boolean;
                                   Final_Block : in     Boolean;
                                   Ctx         : in out Context_Header)
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
      Block           : in     Byte_Seq_Pred;
      Starting_Offset : in     U64;
      Block_Count     : in     Positive_Block_512_Count_T;
      Byte_Count_Add  : in     U64)
     with Global => null,
          Pre  => Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
                  Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count and
                  Block'First = 0 and
                  Add_In_Range (Starting_Offset,
                    ((Block_Count - 1) * Skein_512_Block_Bytes_C) + 63) and
                  Starting_Offset +
                    ((Block_Count - 1) * Skein_512_Block_Bytes_C) + 63 <=
                      Block'Last and
                  Starting_Offset + 63 <= Block'Last,
          Post => Ctx.H.Hash_Bit_Len in Initialized_Hash_Bit_Length and
                  Ctx.H.Hash_Bit_Len = Ctx.H.Hash_Bit_Len'Old and
                  Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count and
                  Ctx.H.Byte_Count = Ctx.H.Byte_Count'Old
   is
      TS   : U64_Seq_3; -- Key schedule: tweak
      KS   : U64_Seq_9; -- Key schedule: chaining vars
      X    : U64_Seq_8; -- Local copy of vars
      W    : U64_Seq_8; -- Local copy of input block

      procedure Initialize_Key_Schedule is
      begin
         --  For speed, we avoid a complete aggregate assignemnt to KS here.
         --  This generates a false-alarm from the flow-analyser, but this is
         --  OK, since type-safety is later re-established by the proof system.

         KS (WCNT_512) := Skein_KS_Parity;

         for I in I8 loop
            KS (I)    := Ctx.X (I);
            --  Compute overall parity
            KS (WCNT_512) := KS (WCNT_512) xor Ctx.X (I);
            pragma Annotate
              (GNATprove, False_Positive, """KS"" might not be initialized",
               "array KS is initialized at index 8, then from 0 to 7");
         end loop;
      end Initialize_Key_Schedule;

      procedure Initialize_TS is
         W0 : U64;
         W1 : U64;
      begin
         W0 := Tweak_To_Words (Ctx.H.Tweak_Words)(0);
         W1 := Tweak_To_Words (Ctx.H.Tweak_Words)(1);
         TS := U64_Seq_3'(0 => W0,
                          1 => W1,
                          2 => W0 xor W1);
      end Initialize_TS;

      procedure Do_First_Key_Injection is
      begin
         X := U64_Seq_8'(0 => W (0) + KS (0),
                         1 => W (1) + KS (1),
                         2 => W (2) + KS (2),
                         3 => W (3) + KS (3),
                         4 => W (4) + KS (4),
                         5 => W (5) + KS (5),
                         6 => W (6) + KS (6),
                         7 => W (7) + KS (7));
         X (WCNT_512 - 3) := X (WCNT_512 - 3) + TS (0);
         X (WCNT_512 - 2) := X (WCNT_512 - 2) + TS (1);
      end Do_First_Key_Injection;

      procedure Threefish_Block
        with Global => (Input  => (KS, TS),
                        In_Out => X)
      is
         procedure Inject_Key (R : in U64) is
            subtype Injection_Range is U64 range 0 .. (WCNT_512 - 1);
         begin
            for I in Injection_Range loop
               X (I) := X (I) + KS ((R + I) mod (WCNT_512 + 1));
            end loop;

            X (WCNT_512 - 3) := X (WCNT_512 - 3) + TS (R mod 3);
            X (WCNT_512 - 2) := X (WCNT_512 - 2) + TS ((R + 1) mod 3);
            X (WCNT_512 - 1) := X (WCNT_512 - 1) + R; -- Avoid slide attacks

            pragma Debug (Trace.Show_Round
                            (S512, Ctx.H, Trace.Skein_Rnd_Key_Inject, X));
         end Inject_Key;

         procedure Round_1 is
         begin
            X (0) := X (0) + X (1);
            X (1) := Rotate_Left (X (1), R_512_0_0);
            X (1) := X (1) xor X (0);

            X (2) := X (2) + X (3);
            X (3) := Rotate_Left (X (3), R_512_0_1);
            X (3) := X (3) xor X (2);

            X (4) := X (4) + X (5);
            X (5) := Rotate_Left (X (5), R_512_0_2);
            X (5) := X (5) xor X (4);

            X (6) := X (6) + X (7);
            X (7) := Rotate_Left (X (7), R_512_0_3);
            X (7) := X (7) xor X (6);
         end Round_1;

         procedure Round_2 is
         begin
            X (2) := X (2) + X (1);
            X (1) := Rotate_Left (X (1), R_512_1_0);
            X (1) := X (1) xor X (2);

            X (4) := X (4) + X (7);
            X (7) := Rotate_Left (X (7), R_512_1_1);
            X (7) := X (7) xor X (4);

            X (6) := X (6) + X (5);
            X (5) := Rotate_Left (X (5), R_512_1_2);
            X (5) := X (5) xor X (6);

            X (0) := X (0) + X (3);
            X (3) := Rotate_Left (X (3), R_512_1_3);
            X (3) := X (3) xor X (0);
         end Round_2;

         procedure Round_3 is
         begin
            X (4) := X (4) + X (1);
            X (1) := Rotate_Left (X (1), R_512_2_0);
            X (1) := X (1) xor X (4);

            X (6) := X (6) + X (3);
            X (3) := Rotate_Left (X (3), R_512_2_1);
            X (3) := X (3) xor X (6);

            X (0) := X (0) + X (5);
            X (5) := Rotate_Left (X (5), R_512_2_2);
            X (5) := X (5) xor X (0);

            X (2) := X (2) + X (7);
            X (7) := Rotate_Left (X (7), R_512_2_3);
            X (7) := X (7) xor X (2);
         end Round_3;

         procedure Round_4 is
         begin
            X (6) := X (6) + X (1);
            X (1) := Rotate_Left (X (1), R_512_3_0);
            X (1) := X (1) xor X (6);

            X (0) := X (0) + X (7);
            X (7) := Rotate_Left (X (7), R_512_3_1);
            X (7) := X (7) xor X (0);

            X (2) := X (2) + X (5);
            X (5) := Rotate_Left (X (5), R_512_3_2);
            X (5) := X (5) xor X (2);

            X (4) := X (4) + X (3);
            X (3) := Rotate_Left (X (3), R_512_3_3);
            X (3) := X (3) xor X (4);
         end Round_4;

         procedure Round_5 is
         begin
            X (0) := X (0) + X (1);
            X (1) := Rotate_Left (X (1), R_512_4_0);
            X (1) := X (1) xor X (0);

            X (2) := X (2) + X (3);
            X (3) := Rotate_Left (X (3), R_512_4_1);
            X (3) := X (3) xor X (2);

            X (4) := X (4) + X (5);
            X (5) := Rotate_Left (X (5), R_512_4_2);
            X (5) := X (5) xor X (4);

            X (6) := X (6) + X (7);
            X (7) := Rotate_Left (X (7), R_512_4_3);
            X (7) := X (7) xor X (6);
         end Round_5;

         procedure Round_6 is
         begin
            X (2) := X (2) + X (1);
            X (1) := Rotate_Left (X (1), R_512_5_0);
            X (1) := X (1) xor X (2);

            X (4) := X (4) + X (7);
            X (7) := Rotate_Left (X (7), R_512_5_1);
            X (7) := X (7) xor X (4);

            X (6) := X (6) + X (5);
            X (5) := Rotate_Left (X (5), R_512_5_2);
            X (5) := X (5) xor X (6);

            X (0) := X (0) + X (3);
            X (3) := Rotate_Left (X (3), R_512_5_3);
            X (3) := X (3) xor X (0);
         end Round_6;

         procedure Round_7 is
         begin
            X (4) := X (4) + X (1);
            X (1) := Rotate_Left (X (1), R_512_6_0);
            X (1) := X (1) xor X (4);

            X (6) := X (6) + X (3);
            X (3) := Rotate_Left (X (3), R_512_6_1);
            X (3) := X (3) xor X (6);

            X (0) := X (0) + X (5);
            X (5) := Rotate_Left (X (5), R_512_6_2);
            X (5) := X (5) xor X (0);

            X (2) := X (2) + X (7);
            X (7) := Rotate_Left (X (7), R_512_6_3);
            X (7) := X (7) xor X (2);
         end Round_7;

         procedure Round_8 is
         begin
            X (6) := X (6) + X (1);
            X (1) := Rotate_Left (X (1), R_512_7_0);
            X (1) := X (1) xor X (6);

            X (0) := X (0) + X (7);
            X (7) := Rotate_Left (X (7), R_512_7_1);
            X (7) := X (7) xor X (0);

            X (2) := X (2) + X (5);
            X (5) := Rotate_Left (X (5), R_512_7_2);
            X (5) := X (5) xor X (2);

            X (4) := X (4) + X (3);
            X (3) := Rotate_Left (X (3), R_512_7_3);
            X (3) := X (3) xor X (4);
         end Round_8;

      begin
         for R in U64 range 1 .. (Skein_512_Rounds_Total / 8) loop
            Round_1;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R-7, X));
            Round_2;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R-6, X));
            Round_3;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R-5, X));
            Round_4;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R-4, X));
            Inject_Key (R * 2 - 1);
            Round_5;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R-3, X));
            Round_6;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R-2, X));
            Round_7;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R-1, X));
            Round_8;
            pragma Debug (Trace.Show_Round (S512, Ctx.H, 8*R,   X));
            Inject_Key (R * 2);
         end loop;
      end Threefish_Block;

      procedure Update_Context is
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

   begin -- Skein_512_Process_Block
      for J in Positive_Block_512_Count_T range 1 .. Block_Count loop
         declare
            Src_Offset : constant U64 :=
              Starting_Offset + (J - 1) * Skein_512_Block_Bytes_C;
         begin
            --  This implementation only supports 2**64 input bytes,
            --  so no carry over to Byte_Count_MSB here.
            Ctx.H.Tweak_Words.Byte_Count_LSB :=
              Ctx.H.Tweak_Words.Byte_Count_LSB + Byte_Count_Add;

            Initialize_Key_Schedule;

            Initialize_TS;

            Get_64_LSB_First (Dst        => W,
                              Src        => Block,
                              Src_Offset => Src_Offset);

            pragma Debug (Trace.Show_Block (Bits         => S512,
                                            H            => Ctx.H,
                                            X            => Ctx.X,
                                            Block        => Block,
                                            Block_Offset => Src_Offset,
                                            W            => W,
                                            KS           => KS,
                                            TS           => TS));

            --  Do the first full key injection
            Do_First_Key_Injection;

            pragma Debug (Trace.Show_Round (Bits => S512,
                                            H    => Ctx.H,
                                            R    => Trace.Skein_Rnd_Key_Initial,
                                            X    => X));

            Threefish_Block;

            --  Do the final "feedforward" xor, update context chaining vars
            Update_Context;

            pragma Debug (Trace.Show_Round
                          (S512, Ctx.H, Trace.Skein_Rnd_Feed_Fwd, Ctx.X));

            Ctx.H.Tweak_Words.First_Block := False;
         end;
      end loop;
   end Skein_512_Process_Block;

   --  Exported subprograms

   function Hash_Bit_Len_Of (Ctx : in Skein_512_Context) return Hash_Bit_Length
   is (Ctx.H.Hash_Bit_Len);

   function Byte_Count_Of   (Ctx : in Skein_512_Context) return U64
   is (Ctx.H.Byte_Count);

   procedure Skein_512_Init (Ctx        :    out Skein_512_Context;
                             HashBitLen : in     Initialized_Hash_Bit_Length)
   is
      Cfg : Skein_512_State_Words;
   begin
      --  Build/Process config block for hashing
      Ctx := Null_Skein_512_Context;

      Ctx.H.Hash_Bit_Len := HashBitLen; -- output has byte count

      Skein_Start_New_Type (Skein_Block_Type_Cfg, True, True, Ctx.H);

      --  Set the schema version, hash result length, and tree info.
      --  All others words are 0
      Cfg := Skein_512_State_Words'
        (0 => To_LittleEndian (Skein_Schema_Ver),
         1 => To_LittleEndian (HashBitLen),
         2 => To_LittleEndian (Skein_Cfg_Tree_Info_Sequential),
         others => 0);

      --  Compute the initial chaining values from config block

      --  First, zero the chaining bytes
      Ctx.X := Skein_512_State_Words'(others => 0);

      Skein_512_Process_Block
        (Ctx             => Ctx,
         Block           => Skein_512_State_Words_To_Bytes (Cfg),
         Starting_Offset => 0,
         Block_Count     => 1,
         Byte_Count_Add  => Skein_Cfg_Str_Len);

      --  Set up to process the data message portion of the hash (default)
      Skein_Start_New_Type (Skein_Block_Type_Msg, True, False, Ctx.H);

   end Skein_512_Init;

   procedure Skein_512_Update (Ctx : in out Skein_512_Context;
                               Msg : in     Byte_Seq_Pred)
   is
      Msg_Byte_Count     : U64;
      N                  : Skein_512_Block_Bytes_Index;
      Block_Count        : Positive_Block_512_Count_T;
      Current_Msg_Offset : U64;
      Bytes_Hashed       : U64;
      Tmp_B              : Skein_512_Block_Bytes;

      procedure Copy_Msg_To_B (Msg_Offset : in     U64;
                               Num_Bytes  : in     U64)
--  UNCOMMENT TO VERIFY Copy_Msg_To_B SEPARATELY
--          with Pre  => Ctx.H.Hash_Bit_Len > 0 and
--                       Msg'First = 0 and
--                       Msg_Offset in Msg'Range and
--                       Add_In_Range (Msg_Offset, Num_Bytes) and
--                       Msg_Offset + Num_Bytes <= Msg'Last + 1 and
--                       Add_In_Range (Ctx.H.Byte_Count, Num_Bytes) and
--                       Ctx.H.Byte_Count + Num_Bytes <= Ctx.B'Last + 1,
--               Post => Ctx.H.Hash_Bit_Len > 0 and
--                       Ctx.H.Hash_Bit_Len = Ctx.H.Hash_Bit_Len'Old and
--                       Ctx.H.Byte_Count = Ctx.H.Byte_Count'Old + Num_Bytes and
--                       Ctx.H.Byte_Count in Skein_512_Block_Bytes_Count
      is
         Src       : U64;
         Dst       : Skein_512_Block_Bytes_Index;
         Final_Dst : Skein_512_Block_Bytes_Index;
         Final_Src : U64;
      begin
         if Num_Bytes > 0 then

            Src := Msg_Offset;

            Dst := Ctx.H.Byte_Count;

            Final_Dst := Dst + (Num_Bytes - 1);

            Final_Src := Src + (Num_Bytes - 1);

            loop
               Ctx.B (Dst) := Msg (Src);

               --  The empty invariant is needed to force GNATprove to cut the
               --  loop just before the exit statement
               pragma Loop_Invariant (True);

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

            --  Compute number of bytes free in Ctx.B
            N := Skein_512_Block_Bytes_C - Ctx.H.Byte_Count;

            Copy_Msg_To_B (Current_Msg_Offset, N);
            Msg_Byte_Count     := Msg_Byte_Count - N;
            Current_Msg_Offset := Current_Msg_Offset + N;

            Tmp_B := Ctx.B;
            Skein_512_Process_Block
              (Ctx             => Ctx,
               Block           => Tmp_B,
               Starting_Offset => 0,
               Block_Count     => 1,
               Byte_Count_Add  => Skein_512_Block_Bytes_C);
            Ctx.H.Byte_Count := 0;
         end if;

         --  Now process any remaining full blocks,
         --  directly from input message data
         if Msg_Byte_Count > Skein_512_Block_Bytes_C then

            --  Number of full blocks to process
            Block_Count := (Msg_Byte_Count - 1) / Skein_512_Block_Bytes_C;

            Skein_512_Process_Block
              (Ctx             => Ctx,
               Block           => Msg,
               Starting_Offset => Current_Msg_Offset,
               Block_Count     => Block_Count,
               Byte_Count_Add  => Skein_512_Block_Bytes_C);

            Bytes_Hashed := Block_Count * Skein_512_Block_Bytes_C;

            Msg_Byte_Count     := Msg_Byte_Count     - Bytes_Hashed;

            Current_Msg_Offset := Current_Msg_Offset + Bytes_Hashed;
         end if;

      end if;

      --  Finally, there might be fewer than Skein_512_Block_Bytes_C bytes left
      --  over that are not yet hashed. Copy these to Ctx.B for processing
      --  in any subsequent call to _Update or _Final.
      Copy_Msg_To_B (Current_Msg_Offset, Msg_Byte_Count);

   end Skein_512_Update;

   procedure Skein_512_Final (Ctx  : in     Skein_512_Context;
                              Hash :    out Byte_Seq_Pred)
   is
      subtype Output_Byte_Count_T  is U64
        range 1 .. (Hash_Bit_Length'Last + 7) / 8;
      subtype Output_Block_Count_T is U64
        range 0 .. (Output_Byte_Count_T'Last + 63) / Skein_512_Block_Bytes_C;
      subtype Positive_Output_Block_Count_T is Output_Block_Count_T
        range 1 .. Output_Block_Count_T'Last;

      Local_Ctx          : Skein_512_Context;
      N                  : U64;
      Blocks_Required    : Positive_Output_Block_Count_T;
      Byte_Count         : Output_Byte_Count_T;
      X                  : Skein_512_State_Words;
      Tmp_B              : Skein_512_Block_Bytes;
      Tmp_Byte_Count_Add : U64;

      procedure Zero_Pad is
      begin
         for I in Skein_512_Block_Bytes_Index
           range Local_Ctx.H.Byte_Count ..
           Skein_512_Block_Bytes_Index'Last loop

            Local_Ctx.B (I) := 0;
         end loop;
      end Zero_Pad;

      procedure Set_Counter (Counter : in U64) is
      begin
         Local_Ctx.B (0) := Byte (Counter and 16#FF#);
         Local_Ctx.B (1) := Byte (Shift_Right (Counter, 8)  and 16#FF#);
         Local_Ctx.B (2) := Byte (Shift_Right (Counter, 16) and 16#FF#);
         Local_Ctx.B (3) := Byte (Shift_Right (Counter, 24) and 16#FF#);
         Local_Ctx.B (4) := Byte (Shift_Right (Counter, 32) and 16#FF#);
         Local_Ctx.B (5) := Byte (Shift_Right (Counter, 40) and 16#FF#);
         Local_Ctx.B (6) := Byte (Shift_Right (Counter, 48) and 16#FF#);
         Local_Ctx.B (7) := Byte (Shift_Right (Counter, 56) and 16#FF#);
      end Set_Counter;

   begin
      Local_Ctx := Ctx;
      Hash := (others => 0);

      Local_Ctx.H.Tweak_Words.Final_Block := True; -- Tag as the final block
      if (Local_Ctx.H.Byte_Count < Skein_512_Block_Bytes_C) then
         Zero_Pad;
      end if;

      Tmp_B := Local_Ctx.B;
      Tmp_Byte_Count_Add := Local_Ctx.H.Byte_Count;

      Skein_512_Process_Block (Ctx             => Local_Ctx,
                               Block           => Tmp_B,
                               Starting_Offset => 0,
                               Block_Count     => 1,
                               Byte_Count_Add  => Tmp_Byte_Count_Add);

      --  Now output the result
      --  Compute the yotal number of output bytes
      Byte_Count := (Local_Ctx.H.Hash_Bit_Len + 7) / 8;

      --  Run Threefish in "counter mode" to generate more output

      --  Zero out Local_Ctx.B, so it can hold the counter
      Local_Ctx.B := Skein_512_Block_Bytes'(others => 0);
      X := Local_Ctx.X; -- Keep a local copy of counter mode "key"

      Blocks_Required := (Byte_Count + 63) / 64;

      for Blocks_Done in 0 .. Blocks_Required - 1 loop
         pragma Loop_Invariant
           (Local_Ctx.H.Hash_Bit_Len = Local_Ctx.H.Hash_Bit_Len'Loop_Entry);

         Set_Counter (Blocks_Done);

         Skein_Start_New_Type (Field_Type  => Skein_Block_Type_Out,
                               First_Block => True,
                               Final_Block => True,
                               Ctx         => Local_Ctx.H);


         --  Run "Counter Mode"
         Tmp_B := Local_Ctx.B;
         Skein_512_Process_Block (Ctx             => Local_Ctx,
                                  Block           => Tmp_B,
                                  Starting_Offset => 0,
                                  Block_Count     => 1,
                                  Byte_Count_Add  => 8);

         --  Number of output bytes left to go
         N := Byte_Count - (Blocks_Done * Skein_512_Block_Bytes_C);
         if (N >= Skein_512_Block_Bytes_C) then
            N := Skein_512_Block_Bytes_C;
         end if;

         --  Push the output Local_Ctx.X into output buffer Hash
         Put_64_LSB_First
           (Dst          => Hash,
            Dst_Offset   => Blocks_Done * Skein_512_Block_Bytes_C,
            Src          => Local_Ctx.X,
            Byte_Count   => N);

         pragma Debug (Trace.Show_Final
                         (Bits         => S512,
                          H            => Local_Ctx.H,
                          Block        => Hash,
                          Byte_Count   => N,
                          Block_Offset =>
                            Blocks_Done * Skein_512_Block_Bytes_C));

         Local_Ctx.X := X; -- restore the counter mode key for next time
      end loop;

   end Skein_512_Final;

   function Skein_512_Hash (Data : in Byte_Seq_Pred) return Skein_512_State_Bytes
   is
      Ctx    : Skein_512_Context;
      Result : Skein_512_State_Bytes;
   begin
      Skein_512_Init (Ctx        => Ctx,
                      HashBitLen => 512);

      Skein_512_Update (Ctx => Ctx,
                        Msg => Data);

      Skein_512_Final (Ctx  => Ctx,
                       Hash => Result);
      return Result;
   end Skein_512_Hash;

   -------------------------------------------------------------------
   --  Debugging control
   -------------------------------------------------------------------

   procedure Set_Debug_Flags (F : in Debug_Flag_Set)
   is
   begin
      pragma Warnings (Off, "statement has no effect");
      Trace.Set_Flags (F);
      pragma Warnings (On,  "statement has no effect");
   end Set_Debug_Flags;

   procedure Show_Msg_8 (Msg   : in String;
                         S     : in Byte_Seq_Pred;
                         Count : in U64)
   is
   begin
      pragma Warnings (Off, "statement has no effect");
      Trace.Show_Msg_8 (Msg, S, Count);
      pragma Warnings (On, "statement has no effect");
   end Show_Msg_8;

end Skein;
