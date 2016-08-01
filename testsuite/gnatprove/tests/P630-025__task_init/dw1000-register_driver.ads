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

with DW1000.BSP;
with DW1000.Types;

--  This package provides an octet-level interface to the DW1000's register
--  set.
package DW1000.Register_Driver
with SPARK_Mode => On
is

   type Operation_Type is (Read, Write) with Size => 1;
   for Operation_Type use (Read => 0, Write => 1);
   --  SPI transaction header Operation bit.

   type Sub_Index_Type is (Not_Present, Present) with Size => 1;
   for Sub_Index_Type use (Not_Present => 0, Present => 1);
   --  SPI transaction header Sub-Index presence bit.

   type Extended_Address_Type is (Not_Extended, Extended) with Size => 1;
   for Extended_Address_Type use (Not_Extended => 0, Extended => 1);
   --  SPI transaction header Extended address bit.
   --
   --  This bit is only used for the 2 octet and 3 octet long headers.


   type Non_Indexed_Header is record
      Register_ID : DW1000.Types.Bits_6 := 0;
      Sub_Index   : Sub_Index_Type      := Not_Present;
      Operation   : Operation_Type      := Read;
   end record
     with Size => 8,
     Dynamic_Predicate => Non_Indexed_Header.Sub_Index = Not_Present;
   --  1-octet SPI transaction header
   --
   --  In this header the Sub_Index field must always be set to Not_Present.

   for Non_Indexed_Header use record
      Register_ID at 0 range 0 .. 5;
      Sub_Index   at 0 range 6 .. 6;
      Operation   at 0 range 7 .. 7;
   end record;

   type Short_Indexed_Header is record
      Register_ID          : DW1000.Types.Bits_6   := 0;
      Sub_Index            : Sub_Index_Type        := Present;
      Operation            : Operation_Type        := Read;
      Register_Sub_Address : DW1000.Types.Bits_7   := 0;
      Extended_Address     : Extended_Address_Type := Not_Extended;
   end record
     with Size => 16,
     Dynamic_Predicate =>
       (Short_Indexed_Header.Sub_Index        = Present and
        Short_Indexed_Header.Extended_Address = Not_Extended);
   --  2-octet SPI transaction header
   --
   --  In this header the Sub_Index field must always be set to Present
   --  and the Extended_Address field must always be set to Not_Extended.


   for Short_Indexed_Header use record
      Register_ID          at 0 range  0 ..  5;
      Sub_Index            at 0 range  6 ..  6;
      Operation            at 0 range  7 ..  7;
      Register_Sub_Address at 0 range  8 .. 14;
      Extended_Address     at 0 range 15 .. 15;
   end record;

   type Long_Indexed_Header is record
      Register_ID              : DW1000.Types.Bits_6   := 0;
      Sub_Index                : Sub_Index_Type        := Present;
      Operation                : Operation_Type        := Read;
      Register_Sub_Address_LSB : DW1000.Types.Bits_7   := 0;
      Extended_Address         : Extended_Address_Type := Extended;
      Register_Sub_Address_MSB : DW1000.Types.Bits_8   := 0;
   end record
     with Size => 24,
     Dynamic_Predicate =>
       (Long_Indexed_Header.Sub_Index        = Present and
        Long_Indexed_Header.Extended_Address = Extended);
   --  3-octet SPI transaction header
   --
   --  In this header the Sub_Index field must always be set to Present
   --  and the Extended_Address field must always be set to Extended.

   for Long_Indexed_Header use record
      Register_ID              at 0 range 0 .. 5;
      Sub_Index                at 0 range 6 .. 6;
      Operation                at 0 range 7 .. 7;
      Register_Sub_Address_LSB at 0 range 8 .. 14;
      Extended_Address         at 0 range 15 .. 15;
      Register_Sub_Address_MSB at 0 range 16 .. 23;
   end record;


   procedure Read_Register(Register_ID : in     DW1000.Types.Bits_6;
                           Sub_Address : in     DW1000.Types.Bits_15;
                           Data        :    out DW1000.Types.Byte_Array)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + (Register_ID, Sub_Address, Data),
                 Data                    => (DW1000.BSP.Device_State,
                                             Register_ID,
                                             Sub_Address)),
     Pre => Data'Length > 0;
   --  Read a register on the DW1000.

   procedure Write_Register(Register_ID : in DW1000.Types.Bits_6;
                            Sub_Address : in DW1000.Types.Bits_15;
                            Data        : in DW1000.Types.Byte_Array)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + (Register_ID, Sub_Address, Data)),
     Pre => Data'Length > 0;
   --  Write to a register on the DW1000.

end DW1000.Register_Driver;
