------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  AIP platform parameters

--# inherit AIP;

package AIP_Support.Platform is
   pragma Pure;

   If_Init_Linkname : constant String := "mintapif_init";
   If_ISR_Linkname  : constant String := "mintapif_isr";

end AIP_Support.Platform;
