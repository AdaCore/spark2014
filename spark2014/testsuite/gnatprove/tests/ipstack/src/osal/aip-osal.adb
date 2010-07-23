------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.ARP;
with AIP.Buffers;
with AIP.Platform;

package body AIP.OSAL is

   procedure If_Init (Err : out Err_T; If_Id : out NIF.Netif_Id);
   pragma Import (C, If_Init, Platform.If_Init_Linkname);
   --  Initialize network interface

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
      Err : Err_T;
   begin
      --  Initialize subsystems

      Buffers.Buffer_Init;
      ARP.Initialize;
      NIF.Initialize;

      --  Set up interfaces

      If_Init (Err, If_Id);

      if Err /= NOERR then
         raise Constraint_Error;
      end if;
   end Initialize;

end AIP.OSAL;
