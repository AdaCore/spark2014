------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package AIP_Pbufs is

   type Pbuf_Id is private;

private

   type Pbuf is array (1 .. 50) of Character;
   type Pbuf_Id is access all Pbuf;

end AIP_Pbufs;
