--
-- Copyright (C) 2017 Nico Huber <nico.h@gmx.de>
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

with HW.Config;

package body HW.PCI.MMConf
with
   Refined_State =>
     (Address_State  =>
        (MM8.Base_Address, MM16.Base_Address, MM32.Base_Address),
      PCI_State      =>
        (MM8.State, MM16.State, MM32.State))
is

   Default_Base_Address : constant Word64 :=
      Calc_Base_Address (Config.Default_MMConf_Base, Dev);

   type Index16 is new Index range 0 .. Index'Last / 2;
   type Index32 is new Index range 0 .. Index'Last / 4;

   type Array8 is array (Index) of Byte with Atomic_Components;
   type Array16 is array (Index16) of Word16 with Atomic_Components;
   type Array32 is array (Index32) of Word32 with Atomic_Components;

   package MM8 is new HW.MMIO_Range
     (Default_Base_Address, Word8, Index, Array8);
   package MM16 is new HW.MMIO_Range
     (Default_Base_Address, Word16, Index16, Array16);
   package MM32 is new HW.MMIO_Range
     (Default_Base_Address, Word32, Index32, Array32);

   procedure Read8 (Value : out Word8; Offset : Index) renames MM8.Read;

   procedure Read16 (Value : out Word16; Offset : Index)
   is
   begin
      MM16.Read (Value, Index16 (Offset / 2));
   end Read16;

   procedure Read32 (Value : out Word32; Offset : Index)
   is
   begin
      MM32.Read (Value, Index32 (Offset / 4));
   end Read32;

   procedure Write8 (Offset : Index; Value : Word8) renames MM8.Write;

   procedure Write16 (Offset : Index; Value : Word16)
   is
   begin
      MM16.Write (Index16 (Offset / 2), Value);
   end Write16;

   procedure Write32 (Offset : Index; Value : Word32)
   is
   begin
      MM32.Write (Index32 (Offset / 4), Value);
   end Write32;

   procedure Set_Base_Address (Base : Word64)
   is
      Base_Address : constant Word64 := Calc_Base_Address (Base, Dev);
   begin
      MM8.Set_Base_Address (Base_Address);
      MM16.Set_Base_Address (Base_Address);
      MM32.Set_Base_Address (Base_Address);
   end Set_Base_Address;

end HW.PCI.MMConf;
