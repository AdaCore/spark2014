------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Internal conversion services for AIP

with System.Storage_Elements;

package body AIP.Conversions is

   ---------
   -- Ofs --
   ---------

   function Ofs (A : System.Address; Offset : Integer) return System.Address is
      use type System.Storage_Elements.Storage_Offset;
   begin
      return A + System.Storage_Elements.Storage_Offset (Offset);
   end Ofs;

end AIP.Conversions;
