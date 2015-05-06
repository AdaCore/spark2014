------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with System.Storage_Elements;

package body AIP.Checksum with
  SPARK_Mode => Off
is

   function Sum_Chunk
     (Data   : System.Address;
      Length : U16_T) return M32_T;
   --  Return the checksum of a single contiguous chunk of data of the given
   --  length, stored at address Data.
   --  Note: result is always in the range of M16_T.

   procedure Swap (S : in out M32_T);
   --  Swap the two low order bytes of S

   procedure Wrap (S : in out M32_T);
   --  Wrap carries in high order bits according to one's complement 16-bit
   --  addition rules.

   ---------------
   -- Sum_Chunk --
   ---------------

   function Sum_Chunk
     (Data   : System.Address;
      Length : U16_T) return M32_T
   is
      use System;
      use System.Storage_Elements;

      Data_A : System.Address;
      Data_I : Integer_Address;
      for Data_I'Address use Data_A'Address;
      pragma Import (Ada, Data_I);

      Result : M32_T;
      Tmp    : M32_T;

      function Get_Byte return M32_T;
      --  Return byte at Data_A

      function Get_Word return M32_T;
      --  Return 16-bit word at Data_A

      --------------
      -- Get_Byte --
      --------------

      function Get_Byte return M32_T is
         Result : M8_T;
         for Result'Address use Data_A;
         pragma Import (Ada, Result);
      begin
         return M32_T (Result);
      end Get_Byte;

      --------------
      -- Get_Word --
      --------------

      function Get_Word return M32_T is
         Result : M16_T;
         for Result'Address use Data_A;
         pragma Import (Ada, Result);
      begin
         return M32_T (Result);
      end Get_Word;

      Odd : Boolean;
      --  True if starting on odd address

      Remain : U16_T;
      --  Remaining length

   --  Start of processing for Sum_Chunk

   begin
      Data_A := Data;
      Result := 0;
      Remain := Length;

      if Data_I mod 2 = 0 then
         Odd := False;
      else
         Odd := True;
         if System.Default_Bit_Order = System.Low_Order_First then
            Result := Get_Byte * 256;
         else
            Result := Get_Byte;
         end if;
         Data_I := Data_I + 1;
         Remain := Remain - 1;
      end if;

      while Data_I mod 4 /= 0 and then Remain >= 2 loop
         Result := Result + Get_Word;
         Data_I := Data_I + 2;
         Remain := Remain - 2;
      end loop;

      if Remain > 7 then
         declare
            Data_32 : array (1 .. Remain / 4) of M32_T;
            for Data_32'Address use Data_A;
            pragma Import (Ada, Data_32);

            Data_32_Index : U16_T := Data_32'First;
         begin
            while Remain > 7 loop
               Tmp := Result + Data_32 (Data_32_Index);
               Data_32_Index := Data_32_Index + 1;
               if Tmp < Result then
                  Tmp := Tmp + 1;
               end if;

               Result := Tmp + Data_32 (Data_32_Index);
               Data_32_Index := Data_32_Index + 1;
               if Result < Tmp then
                  Result := Result + 1;
               end if;

               Remain := Remain - 8;
            end loop;

            Data_I := Data_I
              + 4 * Integer_Address ((Data_32_Index - Data_32'First));
         end;
      end if;

      while Remain > 1 loop
         Result := Result + Get_Word;
         Data_I := Data_I + 2;
         Remain := Remain - 2;
      end loop;

      if Remain /= 0 then
         pragma Assert (Remain = 1);

         if Default_Bit_Order = High_Order_First then
            Result := Result + Get_Byte * 256;
         else
            Result := Result + Get_Byte;
         end if;
      end if;

      Wrap (Result);

      if Odd then
         Swap (Result);
      end if;

      return Result;
   end Sum_Chunk;

   ---------
   -- Sum --
   ---------

   function Sum
     (Buf    : Buffers.Buffer_Id;
      Length : AIP.U16_T) return AIP.M16_T
   is
      use type System.Bit_Order;

      Chunk_Buf    : Buffers.Buffer_Id;
      Chunk_Length : AIP.U16_T;
      Chunk_Data   : System.Address;

      Remain  : AIP.U16_T;
      Swapped : Boolean;
      Result : M32_T;

   begin
      Remain := Length;
      Result := 0;
      Swapped := False;
      Chunk_Buf := Buf;

      while Remain /= 0 loop
         pragma Assert (Chunk_Buf /= Buffers.NOBUF);
         Chunk_Data   := Buffers.Buffer_Payload (Chunk_Buf);
         Chunk_Length := U16_T'Min (Remain, Buffers.Buffer_Len (Chunk_Buf));
         Result := Result + Sum_Chunk (Chunk_Data, Chunk_Length);
         Wrap (Result);
         Remain := Remain - Chunk_Length;
         if Chunk_Length mod 2 /= 0 then
            Swapped := not Swapped;
            Swap (Result);
         end if;
         Chunk_Buf := Buffers.Buffer_Next (Chunk_Buf);
      end loop;

      Wrap (Result);
      if Swapped xor (System.Default_Bit_Order /= System.High_Order_First) then
         Swap (Result);
      end if;
      return M16_T (Result);
   end Sum;

   ----------
   -- Swap --
   ----------

   procedure Swap (S : in out M32_T) is
   begin
      S := (S and 16#ff00#) / 2 ** 8 + (S and 16#ff#) * 2 ** 8;
   end Swap;

   ----------
   -- Wrap --
   ----------

   procedure Wrap (S : in out M32_T) is
   begin
      while S >= 2 ** 16 loop
         S := (S and 16#ffff#) + (S / 2**16);
      end loop;
   end Wrap;

end AIP.Checksum;
