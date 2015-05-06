------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP is

   function No (Err : Err_T) return Boolean is
   begin
      return Err = NOERR;
   end No;

   function Any (Err : Err_T) return Boolean is
   begin
      return not No (Err);
   end Any;

end AIP;
