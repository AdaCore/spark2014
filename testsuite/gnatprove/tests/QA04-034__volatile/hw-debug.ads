--
-- Copyright (C) 2015 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--


package HW.Debug is

   procedure Put (Item : String);
   procedure Put_Line (Item : String);
   procedure New_Line;

   procedure Put_Word8 (Item : Word8);
   procedure Put_Word16 (Item : Word16);
   procedure Put_Word32 (Item : Word32);
   procedure Put_Word64 (Item : Word64);

   procedure Put_Int8 (Item : Int8);
   procedure Put_Int16 (Item : Int16);
   procedure Put_Int32 (Item : Int32);
   procedure Put_Int64 (Item : Int64);

   procedure Put_Reg8 (Name : String; Item : Word8);
   procedure Put_Reg16 (Name : String; Item : Word16);
   procedure Put_Reg32 (Name : String; Item : Word32);
   procedure Put_Reg64 (Name : String; Item : Word64);

   procedure Put_Buffer (Name : String; Buf : in Buffer; Len : in Buffer_Range);

   procedure Set_Register_Write_Delay (Value : Word64);
   Procedure Register_Write_Wait;
end HW.Debug;

--  vim: set ts=8 sts=3 sw=3 et:
