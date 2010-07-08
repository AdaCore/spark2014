------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.OSAL is

   procedure LWIP_Init;
   pragma Import (C, LWIP_Init, "C_init");

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      LWIP_Init;
   end Initialize;

end AIP.OSAL;
