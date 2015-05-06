------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

--  IP stack OS adaptation layer

--  This unit and its children provide the required facilities to integrate
--  the IP stack within its operating environment.

with AIP.NIF;

package AIP.OSAL is

   procedure Initialize;
   --  Initialize the IP stack

private

   If_Id : EID := NIF.IF_NOID;
   --  The OSAL assumes a single interface exists, whose Id is If_Id

end AIP.OSAL;
