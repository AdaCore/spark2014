-------------------------------------------------------------------------------
--  Copyright (c) 2016 Daniel King
--
--  Permission is hereby granted, free of charge, to any person obtaining a
--  copy of this software and associated documentation files (the "Software"),
--  to deal in the Software without restriction, including without limitation
--  the rights to use, copy, modify, merge, publish, distribute, sublicense,
--  and/or sell copies of the Software, and to permit persons to whom the
--  Software is furnished to do so, subject to the following conditions:
--
--  The above copyright notice and this permission notice shall be included in
--  all copies or substantial portions of the Software.
--
--  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
--  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
--  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
--  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
--  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
--  DEALINGS IN THE SOFTWARE.
-------------------------------------------------------------------------------

with Ada.Unchecked_Conversion;

package body DW1000.Register_Driver
with SPARK_Mode => On
is

   subtype Non_Indexed_Header_Bytes   is Types.Byte_Array(1 .. 1);
   subtype Short_Indexed_Header_Bytes is Types.Byte_Array(1 .. 2);
   subtype Long_Indexed_Header_Bytes  is Types.Byte_Array(1 .. 3);

   function To_Bytes is new Ada.Unchecked_Conversion
     (Source => Non_Indexed_Header,
      Target => Non_Indexed_Header_Bytes);

   function To_Bytes is new Ada.Unchecked_Conversion
     (Source => Short_Indexed_Header,
      Target => Short_Indexed_Header_Bytes);

   function To_Bytes is new Ada.Unchecked_Conversion
     (Source => Long_Indexed_Header,
      Target => Long_Indexed_Header_Bytes);

   procedure Read_Register(Register_ID : in     DW1000.Types.Bits_6;
                           Sub_Address : in     DW1000.Types.Bits_15;
                           Data        :    out DW1000.Types.Byte_Array)
   is
      use type Types.Bits_15;

   begin
      if Sub_Address = 0 then
         declare
            Header : constant Non_Indexed_Header := Non_Indexed_Header'
              (Operation   => Read,
               Sub_Index   => Not_Present,
               Register_ID => Register_ID);
         begin
            BSP.Read_Transaction(Header => To_Bytes (Header),
                                 Data   => Data);
         end;

      elsif Sub_Address < 2**7 then
         declare
            Header : constant Short_Indexed_Header := Short_Indexed_Header'
              (Operation            => Read,
               Sub_Index            => Present,
               Register_ID          => Register_ID,
               Extended_Address     => Not_Extended,
               Register_Sub_Address => Types.Bits_7 (Sub_Address));
         begin
            BSP.Read_Transaction(Header => To_Bytes (Header),
                                 Data   => Data);
         end;

      else
         declare
            Header : constant Long_Indexed_Header := Long_Indexed_Header'
              (Operation                => Read,
               Sub_Index                => Present,
               Register_ID              => Register_ID,
               Extended_Address         => Extended,
               Register_Sub_Address_LSB => Types.Bits_7 (Sub_Address and 16#7F#),
               Register_Sub_Address_MSB => Types.Bits_8 (Sub_Address / 2**7));
         begin
            BSP.Read_Transaction(Header => To_Bytes (Header),
                                 Data   => Data);
         end;

      end if;
   end Read_Register;

   procedure Write_Register(Register_ID : in DW1000.Types.Bits_6;
                            Sub_Address : in DW1000.Types.Bits_15;
                            Data        : in DW1000.Types.Byte_Array)
   is
      use type Types.Bits_15;

   begin
      if Sub_Address = 0 then
         declare
            Header : constant Non_Indexed_Header := Non_Indexed_Header'
              (Operation   => Write,
               Sub_Index   => Not_Present,
               Register_ID => Register_ID);
         begin
            BSP.Write_Transaction(Header => To_Bytes (Header),
                                  Data   => Data);
         end;

      elsif Sub_Address < 2**7 then
         declare
            Header : constant Short_Indexed_Header := Short_Indexed_Header'
              (Operation            => Write,
               Sub_Index            => Present,
               Register_ID          => Register_ID,
               Extended_Address     => Not_Extended,
               Register_Sub_Address => Types.Bits_7 (Sub_Address));
         begin
            BSP.Write_Transaction(Header => To_Bytes (Header),
                                  Data   => Data);
         end;

      else
         declare
            Header : constant Long_Indexed_Header := Long_Indexed_Header'
              (Operation                => Write,
               Sub_Index                => Present,
               Register_ID              => Register_ID,
               Extended_Address         => Extended,
               Register_Sub_Address_LSB => Types.Bits_7 (Sub_Address and 16#7F#),
               Register_Sub_Address_MSB => Types.Bits_8 (Sub_Address / 2**7));
         begin
            BSP.Write_Transaction(Header => To_Bytes (Header),
                                  Data   => Data);
         end;
      end if;
   end Write_Register;

end DW1000.Register_Driver;
