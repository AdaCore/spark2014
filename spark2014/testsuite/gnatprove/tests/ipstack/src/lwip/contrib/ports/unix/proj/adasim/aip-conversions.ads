------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System, Ada.Unchecked_Conversion;

package AIP.Conversions is

   function To_IPTR is
      new Ada.Unchecked_Conversion (System.Address, AIP.IPTR_T);

end AIP.Conversions;

