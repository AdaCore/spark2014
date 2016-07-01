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

with DW1000.Generic_RO_Register_Driver;
with DW1000.Generic_WO_Register_Driver;

package body DW1000.Generic_RW_Register_Driver
is

   -- Reuse the Read/Write procedures from the other drivers.
   package Read_Driver is new Generic_RO_Register_Driver
     (Register_Type,
      Register_ID,
      Sub_Register);

   package Write_Driver is new Generic_WO_Register_Driver
     (Register_Type,
      Register_ID,
      Sub_Register);


   procedure Read(Reg : out Register_Type)
   is
   begin
      Read_Driver.Read(Reg);
   end Read;


   procedure Write(Reg : in Register_Type)
   is
   begin
      Write_Driver.Write(Reg);
   end Write;

end DW1000.Generic_RW_Register_Driver;
