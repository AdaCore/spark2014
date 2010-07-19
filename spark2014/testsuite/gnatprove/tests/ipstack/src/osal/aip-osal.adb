------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP_Support.Platform;

package body AIP.OSAL is

   function If_Init return Err_T;
   pragma Import (C, If_Init, AIP_Support.Platform.If_Init_Linkname);
   --  Initialize network interface

   ----------------
   -- Initialize --
   ----------------

   procedure Initialize is
   begin
      if If_Init /= NOERR then
         raise Constraint_Error;
      end if;
   end Initialize;

end AIP.OSAL;
