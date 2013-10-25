package body Skein
   with SPARK_Mode
is

   package Trace
     with SPARK_Mode => On
   is

      procedure Set_Flags (F : in Skein.Debug_Flag_Set)
        with Depends => (null => F);

   end Trace;

   procedure Put_64_LSB_First (Dst        : in out Byte_Seq;
                               Dst_Offset : in     U64;
                               Src        : in     U64_Seq;
                               Byte_Count : in     U64)
   is
   begin
      -- Flow analysis all OK for this unit
      
      pragma Warnings (Off, "no Global contract*");
      if Byte_Count >= 1 then
         for N in U64 range 0 .. (Byte_Count - 1) loop
            Dst (Dst_Offset + N) := Byte (Interfaces.Shift_Right -- warning here suppressed
                                            (Interfaces.Unsigned_64 (Src (N / 8)),
                                             Natural (8 * (N and 7))) and 16#FF#);
         end loop;
      end if;
      pragma Warnings (On, "no Global contract*");
   end Put_64_LSB_First;
   pragma Inline (Put_64_LSB_First);


   procedure Get_64_LSB_First (Dst        :    out U64_Seq;
                               Src        : in     Byte_Seq;
                               Src_Offset : in     U64)
   is
      Dst_Index : Word_Count_T;
      Src_Index : U64;
   begin
      pragma Warnings (Off, "no Global contract*");

      Dst_Index := 0;
      Src_Index := Src_Offset;
      loop

	 -- Expect a flow error here - proves that IFA is happening!

         Dst (Dst_Index) :=
           U64 (Src (Src_Index)) +
           Interfaces.Shift_Left (U64 (Src (Src_Index + 1)), 8) +
           Interfaces.Shift_Left (U64 (Src (Src_Index + 2)), 16) +
           Interfaces.Shift_Left (U64 (Src (Src_Index + 3)), 24) +
           Interfaces.Shift_Left (U64 (Src (Src_Index + 4)), 32) +
           Interfaces.Shift_Left (U64 (Src (Src_Index + 5)), 40) +
           Interfaces.Shift_Left (U64 (Src (Src_Index + 6)), 48) +
           Interfaces.Shift_Left (U64 (Src (Src_Index + 7)), 56);

         exit when Dst_Index = Dst'Last;

         Dst_Index := Dst_Index + 1;
         Src_Index := Src_Index + 8;
      end loop;

      pragma Warnings (On, "no Global contract*");
   end Get_64_LSB_First;
   pragma Inline (Get_64_LSB_First);




   -- Following this stub, all analysis seems to stop!
   package body Trace is separate;
   


   procedure Skein_512_Init (Ctx        :    out Skein_512_Context;
                             HashBitLen : in     Initialized_Hash_Bit_Length)

   is
      Cfg : Skein_512_State_Words;
   begin
      -- Commenting out the next line to force a flow error.
      -- This SHOULD be spotted by IFA...
      -- Ctx := Null_Skein_512_Context;

      Ctx.H.Hash_Bit_Len := HashBitLen; -- output has byte count

      -- Set the schema version, hash result length, and tree info.
      -- All others words are 0
      Cfg := Skein_512_State_Words'(0 => 0,
                                    1 => HashBitLen,
                                    2 => 0,
                                    others => 0);

      -- Compute the initial chaining values from config block

      -- First, zero the chaining bytes
      Ctx.X := Skein_512_State_Words'(others => 0);

   end Skein_512_Init;

end Skein;
