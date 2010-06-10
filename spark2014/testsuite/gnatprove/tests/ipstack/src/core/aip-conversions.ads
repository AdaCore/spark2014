------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Internal conversion services for AIP

with System, Ada.Unchecked_Conversion;

package AIP.Conversions is

   --  System.Address / IPTR conversions are required for LWIP binding
   --  purposes, in particular callback subprogram addresses.

   function To_IPTR is
      new Ada.Unchecked_Conversion (System.Address, AIP.IPTR_T);

end AIP.Conversions;
