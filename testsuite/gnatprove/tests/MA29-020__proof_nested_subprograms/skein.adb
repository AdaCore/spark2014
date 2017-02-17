with Ada.Unchecked_Conversion;

package body Skein
   with SPARK_Mode
is

   -- Number of rounds for the different block sizes
   Skein_512_Rounds_Total : constant := 72;

   -- Skein_512 round rotation constants
   subtype Rotation_Count is Natural range 2 .. 60;

   Skein_Version      : constant := 1;
   Skein_ID_String_LE : constant U32 := 16#33414853#; -- "SHA3" (little endian)

   Skein_Schema_Ver   : constant U64 := (U64 (Skein_Version) * 2**32) +
                                            U64 (Skein_ID_String_LE);

   -- Revised Key Schedule Parity constant "C240" from version 1.3
   -- of the Skein specification.
   Skein_KS_Parity    : constant U64 := 16#1BD11BDA_A9FC1A22#;

   Skein_Cfg_Tree_Info_Sequential : constant := 0;

   Skein_Cfg_Str_Len : constant := 4*8;

   procedure Put_64_LSB_First (Dst        : in out Byte_Seq;
                               Dst_Offset : in     U64;
                               Src        : in     U64_Seq;
                               Byte_Count : in     U64)
   is
   begin
      if Byte_Count >= 1 then
         for N in U64 range 0 .. (Byte_Count - 1) loop
            Dst (Dst_Offset + N) := Byte (Interfaces.Shift_Right -- warning here suppressed
                                            (Interfaces.Unsigned_64 (Src (N / 8)),
                                             Natural (8 * (N and 7))) and 16#FF#);
         end loop;
      end if;
   end Put_64_LSB_First;

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

   -- this version is marked as "proved" in gnatprove.out
   procedure Zero_Pad (Start_Index : in     Skein_512_Block_Bytes_Index;
                       Ctx         : in out Skein_512_Context)
   is
   begin
      for I in Skein_512_Block_Bytes_Index range Start_Index .. Skein_512_Block_Bytes_Index'Last loop
	 Ctx.B (I) := 0;
      end loop;
   end Zero_Pad;

   procedure Skein_512_Final (Ctx  : in     Skein_512_Context;
                              Hash :    out Byte_Seq)
   is
      subtype Output_Byte_Count_T  is U64 range 1 .. (Hash_Bit_Length'Last + 7) / 8;
      subtype Output_Block_Count_T is U64 range 0 .. (Output_Byte_Count_T'Last + 63) / Skein_512_Block_Bytes_C;
      subtype Positive_Output_Block_Count_T is Output_Block_Count_T range 1 .. Output_Block_Count_T'Last;

      Local_Ctx          : Skein_512_Context;
      N                  : U64;
      Blocks_Done        : Output_Block_Count_T;
      Blocks_Required    : Positive_Output_Block_Count_T;
      Byte_Count         : Output_Byte_Count_T;
      X                  : Skein_512_State_Words;

      -- This version is marked as "skipped" in gnatprove.out
      procedure Zero_Pad_B
      is
      begin
         for I in Skein_512_Block_Bytes_Index range Local_Ctx.H.Byte_Count .. Skein_512_Block_Bytes_Index'Last loop
            Local_Ctx.B (I) := 0;
         end loop;
      end Zero_Pad_B;

      procedure Set_B_Counter (Counter : in U64)
      is
      begin
         Local_Ctx.B (0) := Byte (Counter and 16#FF#);
         Local_Ctx.B (1) := Byte (Interfaces.Shift_Right (Counter, 8)  and 16#FF#);
         Local_Ctx.B (2) := Byte (Interfaces.Shift_Right (Counter, 16) and 16#FF#);
         Local_Ctx.B (3) := Byte (Interfaces.Shift_Right (Counter, 24) and 16#FF#);
         Local_Ctx.B (4) := Byte (Interfaces.Shift_Right (Counter, 32) and 16#FF#);
         Local_Ctx.B (5) := Byte (Interfaces.Shift_Right (Counter, 40) and 16#FF#);
         Local_Ctx.B (6) := Byte (Interfaces.Shift_Right (Counter, 48) and 16#FF#);
         Local_Ctx.B (7) := Byte (Interfaces.Shift_Right (Counter, 56) and 16#FF#);
      end Set_B_Counter;

   begin
      Local_Ctx := Ctx;
      Hash := (others => 0);

      Local_Ctx.H.Tweak_Words.Final_Block := True; -- Tag as the final block
      if (Local_Ctx.H.Byte_Count < Skein_512_Block_Bytes_C) then
         Zero_Pad_B;
      end if;

      -- Now output the result
      Byte_Count := (Local_Ctx.H.Hash_Bit_Len + 7) / 8; -- Total number of output bytes

      -- Run Threefish in "counter mode" to generate more output
      Local_Ctx.B := Skein_512_Block_Bytes'(others => 0); -- Zero out Local_Ctx.B, so it can hold the counter
      X := Local_Ctx.X; -- Keep a local copy of counter mode "key"

      Blocks_Required := (Byte_Count + 63) / 64;
      Blocks_Done := 0;

      loop
         Set_B_Counter (Blocks_Done);

         Skein_Start_New_Type (Field_Type  => Skein_Block_Type_Out,
                               First_Block => True,
                               Final_Block => True,
                               Ctx         => Local_Ctx.H);


         N := Byte_Count - (Blocks_Done * Skein_512_Block_Bytes_C); -- number of output bytes left to go
         if (N >= Skein_512_Block_Bytes_C) then
            N := Skein_512_Block_Bytes_C;
         end if;

         -- Push the output Local_Ctx.X into output buffer Hash
         Put_64_LSB_First (Dst          => Hash,
                           Dst_Offset   => Blocks_Done * Skein_512_Block_Bytes_C,
                           Src          => Local_Ctx.X,
                           Byte_Count   => N);

         Local_Ctx.X := X; -- restore the counter mode key for next time

         Blocks_Done := Blocks_Done + 1;
         exit when Blocks_Done >= Blocks_Required;

      end loop;

   end Skein_512_Final;


end Skein;
