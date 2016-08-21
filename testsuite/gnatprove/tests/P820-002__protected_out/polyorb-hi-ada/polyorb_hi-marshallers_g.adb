------------------------------------------------------------------------------
--                                                                          --
--                          PolyORB HI COMPONENTS                           --
--                                                                          --
--             P O L Y O R B _ H I . M A R S H A L L E R S _ G              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--    Copyright (C) 2006-2009 Telecom ParisTech, 2010-2016 ESA & ISAE.      --
--                                                                          --
-- PolyORB-HI is free software; you can redistribute it and/or modify under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. PolyORB-HI is distributed in the hope that it will be useful, but  --
-- WITHOUT ANY WARRANTY; without even the implied warranty of               --
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
--              PolyORB-HI/Ada is maintained by the TASTE project           --
--                      (taste-users@lists.tuxfamily.org)                   --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Unchecked_Conversion;
with PolyORB_HI.Streams;

package body PolyORB_HI.Marshallers_G
  with SPARK_Mode => Off --  XXX because of 'Object_Size
is
   use type PolyORB_HI.Streams.Stream_Element_Offset;

   Data_Size : constant PolyORB_HI.Streams.Stream_Element_Offset
     := Data_Type'Object_Size / 8;

   subtype Data_Type_Stream is
     PolyORB_HI.Streams.Stream_Element_Array (1 .. Data_Size);

   function Data_Type_To_Stream is
      new Ada.Unchecked_Conversion (Data_Type, Data_Type_Stream);
   function Stream_To_Data_Type is
      new Ada.Unchecked_Conversion (Data_Type_Stream, Data_Type);

   --------------
   -- Marshall --
   --------------

   procedure Marshall
     (R :        Data_Type;
      M : in out Messages.Message_Type)
   is
      Data : constant Data_Type_Stream := Data_Type_To_Stream (R);

   begin
      Messages.Write (M, Data);
   end Marshall;

   ----------------
   -- Unmarshall --
   ----------------

   procedure Unmarshall
     (R :    out Data_Type;
      M : in out Messages.Message_Type)
   is
      Data : PolyORB_HI.Streams.Stream_Element_Array (1 .. Data_Size);
      Last : PolyORB_HI.Streams.Stream_Element_Offset;
   begin
      Messages.Read (M, Data, Last);

      if Last = Data_Size then --  XXX Data'Size [attribute]
         R := Stream_To_Data_Type (Data_Type_Stream (Data));
      end if;
   end Unmarshall;

end PolyORB_HI.Marshallers_G;
