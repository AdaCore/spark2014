------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP is

   function No (Err : Err_T) return Boolean is
   begin
      return Err = AIP.NOERR;
   end No;

   function Some (Err : Err_T) return Boolean is
   begin
      return not No (Err);
   end Some;

end AIP;
