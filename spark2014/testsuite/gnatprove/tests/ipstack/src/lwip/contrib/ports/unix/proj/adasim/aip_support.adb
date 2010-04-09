------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP_Support is
   procedure Assert (T : Boolean) is
   begin
      if not T then
         raise Program_Error;
      end if;
   end Assert;
end AIP_Support;
