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

generic
   Dev : PCI.Address := (0, 0, 0);
package HW.PCI.Dev
with
   Abstract_State => (Address_State, (PCI_State with External)),
   Initializes => Address_State
is

   procedure Read8 (Value : out Word8; Offset : Index);
   procedure Read16 (Value : out Word16; Offset : Index)
   with
      Pre => Offset mod 2 = 0;
   procedure Read32 (Value : out Word32; Offset : Index)
   with
      Pre => Offset mod 4 = 0;

   procedure Write8 (Offset : Index; Value : Word8);
   procedure Write16 (Offset : Index; Value : Word16)
   with
      Pre => Offset mod 2 = 0;
   procedure Write32 (Offset : Index; Value : Word32)
   with
      Pre => Offset mod 4 = 0;

   pragma Warnings (GNATprove, Off, "unused variable ""WC""*",
                    Reason => "Used for a common interface");
   procedure Map
     (Addr     :    out Word64;
      Res      : in     Resource;
      Length   : in     Natural := 0;
      Offset   : in     Natural := 0;
      WC       : in     Boolean := False);
   pragma Warnings (GNATprove, On, "unused variable ""WC""*");

   procedure Resource_Size (Length : out Natural; Res : Resource);

   pragma Warnings (GNATprove, Off, "unused variable ""MMConf_Base""*",
                    Reason => "Used for a common interface");
   procedure Initialize (Success : out Boolean; MMConf_Base : Word64 := 0);
   pragma Warnings (GNATprove, On, "unused variable ""MMConf_Base""*");

end HW.PCI.Dev;
