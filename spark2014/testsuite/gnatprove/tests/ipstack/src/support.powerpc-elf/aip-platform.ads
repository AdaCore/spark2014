------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  AIP platform parameters

--# inherit AIP;

package AIP.Platform is
   pragma Pure;

   If_Init_Linkname : constant String := "ne2kif_init";
   If_ISR_Linkname  : constant String := "ne2kif_isr";

end AIP.Platform;
