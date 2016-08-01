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

--  This package provides a generic API for typed write-only registers.
--
--  Register_Type is the typed representation of the register (e.g. a record
--  with a representation clause matching the layout of the register according
--  to the DW1000 User Manual).
--
--  Register_ID is the numerical ID of the register file according to the
--  DW1000 User Manual.
--
--  Sub_Register is the offset of the sub-register within the register file.
--  If the register file has no sub-registers then this should be set to 0.
generic
   type Register_Type is private;
   Register_ID  : DW1000.Types.Bits_6;
   Sub_Register : DW1000.Types.Bits_15 := 0;
package DW1000.Generic_WO_Register_Driver
is

   procedure Write(Reg : in Register_Type)
     with Global => (In_Out => DW1000.BSP.Device_State),
     Depends => (DW1000.BSP.Device_State => + Reg),
     SPARK_Mode => On;

end DW1000.Generic_WO_Register_Driver;
