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
with HW.PCI.MMConf;

with HW.MMIO_Range;
pragma Elaborate_All (HW.MMIO_Range);

package body HW.PCI.Dev
with
   Refined_State =>
     (Address_State  => MM.Address_State,
      PCI_State      => MM.PCI_State)
is

   package MM is new HW.PCI.MMConf (Dev);

   procedure Read8 (Value : out Word8; Offset : Index) renames MM.Read8;
   procedure Read16 (Value : out Word16; Offset : Index) renames MM.Read16;
   procedure Read32 (Value : out Word32; Offset : Index) renames MM.Read32;

   procedure Write8 (Offset : Index; Value : Word8) renames MM.Write8;
   procedure Write16 (Offset : Index; Value : Word16) renames MM.Write16;
   procedure Write32 (Offset : Index; Value : Word32) renames MM.Write32;

   procedure Map
     (Addr     :    out Word64;
      Res      : in     Resource;
      Length   : in     Natural := 0;
      Offset   : in     Natural := 0;
      WC       : in     Boolean := False)
   is
      use type HW.Word8;
      use type HW.Word32;

      Header_Type : Word8;
      Reg32       : Word32;
   begin
      Addr := 0;
      Read8 (Header_Type, PCI.Header_Type);
      if (Header_Type and Header_Type_Mask) = Header_Type_Normal then
         Read32 (Reg32, Base_Address (Res));
         if (Reg32 and Base_Address_Space_Mask) = Base_Address_Space_Mem then
            case Reg32 and Base_Address_Mem_Type_Mask is
               when Base_Address_Mem_Type_64 =>
                  if Res < Res5 then
                     Addr := Word64 (Reg32 and Base_Address_Mem_Mask);
                     Read32 (Reg32, Base_Address (Resource'Succ (Res)));
                     Addr := Addr or Shift_Left (Word64 (Reg32), 32);
                  end if;
               when others =>
                  Addr := Word64 (Reg32 and Base_Address_Mem_Mask);
            end case;
         end if;
      end if;
      if Addr /= 0 then
         if Length = 0 or else
            Addr <= Word64'Last - Word64 (Length) - Word64 (Offset) + 1
         then
            Addr := Addr + Word64 (Offset);
         else
            Addr := 0;
         end if;
      end if;
   end Map;

   procedure Resource_Size (Length : out Natural; Res : Resource)
   is
      use Type HW.Word16;
      use Type HW.Word32;

      Cmd : Word16;
      Base, Backup : Word32;
   begin
      Length := 0;

      Read16 (Cmd, PCI.Command);
      Write16 (PCI.Command, Cmd and not PCI.Command_Memory);

      Read32 (Backup, Base_Address (Res));
      if (Backup and Base_Address_Space_Mask) = Base_Address_Space_Mem then
         Write32 (Base_Address (Res), 16#ffff_ffff#);
         Read32 (Base, Base_Address (Res));
         Base := not (Base and Base_Address_Mem_Mask) + 1;
         if Base <= Word32 (Natural'Last) then
            Length := Natural (Base);
         end if;
         Write32 (Base_Address (Res), Backup);
      end if;

      Write16 (PCI.Command, Cmd);
   end Resource_Size;

   procedure Initialize (Success : out Boolean; MMConf_Base : Word64 := 0)
   is
   begin
      if MMConf_Base /= 0 then
         MM.Set_Base_Address (MMConf_Base);
      else
         MM.Set_Base_Address (Config.Default_MMConf_Base);
      end if;
      Success := MMConf_Base /= 0 or Config.Default_MMConf_Base_Set;
   end Initialize;

end HW.PCI.Dev;
