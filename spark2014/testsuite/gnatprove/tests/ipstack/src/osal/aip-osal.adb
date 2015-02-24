------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2015, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with System;

with AIP.ARP;
with AIP.Buffers;
with AIP.Config;
with AIP.Platform;
with AIP.TCP;
with AIP.UDP;

package body AIP.OSAL is

   procedure If_Init
     (Params : System.Address;
      Err    : out Err_T;
      If_Id  : out NIF.Netif_Id);
   pragma Import (C, If_Init, Platform.If_Init_Linkname);
   --  Initialize network interface. Params is a null-terminated C string.
   --  The interface's initialization routine is responsible for requesting
   --  allocation of a Netif_Id from the NIF subsystem.

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
      Err : Err_T;
   begin
      --  Initialize subsystems

      Buffers.Buffer_Init;
      UDP.UDP_Init;
      TCP.TCP_Init;
      ARP.Initialize;
      NIF.Initialize;

      --  Set up interfaces

      If_Init (Config.Interface_Parameters, Err, If_Id);

      if Any (Err) then
         raise Constraint_Error;
      end if;
   end Initialize;

end AIP.OSAL;
