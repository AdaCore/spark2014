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

with DW1000.Types;

--  This package defines low-level procedures for interfacing with the DW1000
--  at the physical layer.
--
--  The body for this package is not included in this project as it is very
--  specific to the target hardware. Therefore, the body for this package
--  must be implemented by the user for their target board.
package DW1000.BSP
with SPARK_Mode => On,
  Abstract_State => (Device_State with External),
  Initializes    => Device_State
is

   procedure Reset_DW1000
     with Global => (Output => Device_State),
     Depends => (Device_State => null);
   --  Resets the DW1000 via the RSTn line.

   procedure Write_Transaction(Header : in DW1000.Types.Byte_Array;
                               Data   : in DW1000.Types.Byte_Array)
     with Global => (In_Out => Device_State),
     Depends => (Device_State => + (Header, Data)),
     Pre => (Header'Length in 1 .. 3
             and Data'Length > 0);
   --  Perform a "write" transaction to the DW1000.
   --
   --  This procedure executes a write transaction by performing the following
   --  steps:
   --     1. Select the DW1000 on the SPI bus.
   --     2. Send the transaction header bytes (1 .. 3 bytes) via the SPI
   --        interface.
   --     3. Send the transaction data (variable length) to the DW1000 via the
   --        SPI interface.
   --     4. Deselect the DW1000 on the SPI bus.
   --
   --  Note: This procedure must not block. I.e. the procedure must not use
   --  the 'delay until' statement, nor call any protected entries.

   procedure Read_Transaction(Header : in     DW1000.Types.Byte_Array;
                              Data   :    out DW1000.Types.Byte_Array)
     with Global => (In_Out => Device_State),
     Depends => (Device_State => + (Header, Data),
                 Data         => (Header, Device_State)),
     Pre => (Header'Length in 1 .. 3
             and Data'Length > 0);
   --  Perform a "read" transaction from the DW1000.
   --
   --  This procedure executes a write transaction by performing the following
   --  steps:
   --     1. Select the DW1000 on the SPI bus.
   --     2. Send the transaction header bytes (1 .. 3 bytes) via the SPI
   --        interface.
   --     3. Read the transaction data (variable length) from the DW1000 via
   --        the SPI interface, and write the received bytes to the 'Data' byte
   --        array.
   --     4. Deselect the DW1000 on the SPI bus.
   --
   --  Note: This procedure must not block. I.e. the procedure must not use
   --  the 'delay until' statement, nor call any protected entries.

end DW1000.BSP;
