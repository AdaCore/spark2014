------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  Initialization

package body AIP.Init is

   procedure LWIP_init;
   pragma Import (C, LWIP_init, "C_init");

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      LWIP_Init;
   end Initialize;

end AIP.Init;
