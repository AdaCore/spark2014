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

package HW.PCI
is

   type Bus is range 0 .. 255;
   type Slot is range 0 .. 31;
   type Func is range 0 ..  7;

   type Address is record
      Bus   : PCI.Bus;
      Slot  : PCI.Slot;
      Func  : PCI.Func;
   end record;

   type Index is range 0 .. 4095;

   Vendor_Id                     : constant Index := 16#00#;
   Device_Id                     : constant Index := 16#02#;
   Command                       : constant Index := 16#04#;
      Command_Memory             : constant := 16#02#;
   Header_Type                   : constant Index := 16#0e#;
      Header_Type_Mask           : constant := 16#7f#;
      Header_Type_Normal         : constant := 16#00#;

   type Resource is (Res0, Res1, Res2, Res3, Res4, Res5);
   Base_Address : constant array (Resource) of Index :=
     (16#10#, 16#14#, 16#18#, 16#1c#, 16#20#, 16#24#);
      Base_Address_Space_Mask    : constant := 1 * 2 ** 0;
      Base_Address_Space_IO      : constant := 1 * 2 ** 0;
      Base_Address_Space_Mem     : constant := 0 * 2 ** 0;
      Base_Address_Mem_Type_Mask : constant := 3 * 2 ** 1;
      Base_Address_Mem_Type_32   : constant := 0 * 2 ** 1;
      Base_Address_Mem_Type_1M   : constant := 1 * 2 ** 1;
      Base_Address_Mem_Type_64   : constant := 2 * 2 ** 1;
      Base_Address_Mem_Prefetch  : constant := 1 * 2 ** 3;
      Base_Address_IO_Mask       : constant := 16#ffff_fffc#;
      Base_Address_Mem_Mask      : constant := 16#ffff_fff0#;

private
   use type HW.Word64;
   function Calc_Base_Address (Base_Addr : Word64; Dev : Address) return Word64
   is
     (Base_Addr +
      Word64 (Dev.Bus) * 32 * 8 * 4096 +
      Word64 (Dev.Slot) * 8 * 4096 +
      Word64 (Dev.Func) * 4096);

end HW.PCI;
