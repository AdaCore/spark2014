------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;

with AIP.ARP;
with AIP.Buffers;
with AIP.Config;
with AIP.IPaddrs;
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

      If_Remote_IP : constant IPaddrs.IPaddr :=
                       192 * 2 ** 24 + 168 * 2 ** 16 + 0 * 2 ** 8 + 1;
      If_IP        : constant IPaddrs.IPaddr := If_Remote_IP + 1;
      If_Mask      : constant IPaddrs.IPaddr := 16#ffffff00#;

   begin
      --  Initialize subsystems

      Buffers.Buffer_Init;
      UDP.UDP_Init;
      TCP.TCP_Init;
      ARP.Initialize;
      NIF.Initialize;

      --  Set up interfaces

      If_Init (Config.Interface_Parameters, Err, If_Id);

      if No (Err) then
         NIF.If_Config
           (Nid       => If_Id,
            IP        => If_IP,
            Mask      => If_Mask,
            Broadcast => (If_IP and If_Mask) + 16#ff#,
            Remote    => If_Remote_IP,
            Err       => Err);
      end if;

      if Any (Err) then
         raise Constraint_Error;
      end if;
   end Initialize;

end AIP.OSAL;
