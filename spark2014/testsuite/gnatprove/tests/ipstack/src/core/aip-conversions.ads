------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Internal conversion services for AIP

with System;

package AIP.Conversions is

   pragma Preelaborate;

   function Ofs (A : System.Address; Offset : Integer) return System.Address;
   --  Return A + Offset

end AIP.Conversions;
