------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Support is

   --# hide AIP.Support;

   procedure Verify (T : Boolean) is
   begin
      if not T then
         raise Program_Error;
      end if;
   end Verify;

end AIP.Support;
