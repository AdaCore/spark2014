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

with DW1000.Register_Driver;

package body DW1000.Generic_RO_Register_Driver
is
   subtype Register_Byte_Array is DW1000.Types.Byte_Array(1 .. Register_Type'Size / 8);

   procedure Deserialize(Source : in     Register_Byte_Array;
                         Target :    out Register_Type)
     with Inline,
     Depends => (Target => Source),
     SPARK_Mode => On;


   procedure Deserialize(Source : in     Register_Byte_Array;
                         Target :    out Register_Type)
     with SPARK_Mode => Off
   is
      Target_Bytes : Register_Byte_Array
        with Import,
        Convention => Ada,
        Address => Target'Address;

   begin
      Target_Bytes := Source;
   end Deserialize;


   procedure Read(Reg : out Register_Type)
   is
      Reg_Bytes : Register_Byte_Array;

   begin
      DW1000.Register_Driver.Read_Register(Register_ID, Sub_Register, Reg_Bytes);

      Deserialize(Source => Reg_Bytes,
                  Target => Reg);
   end Read;

end DW1000.Generic_RO_Register_Driver;
