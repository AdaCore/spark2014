------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--  AIP configuration parameters

--# inherit AIP;

with System;

package AIP.Config is
   use type System.Bit_Order;

   HOST_BIG_ENDIAN : constant Boolean :=
                       (System.Default_Bit_Order = System.High_Order_First);

   TCP_DEFAULT_LISTEN_BACKLOG : constant := 5;
end AIP.Config;
