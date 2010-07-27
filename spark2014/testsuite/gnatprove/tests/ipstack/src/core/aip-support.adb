------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package body AIP.Support is

   procedure Verify (T : Boolean) is
      --# hide Verify;
   begin
      if not T then
         raise Program_Error;
      end if;
   end Verify;

   procedure Verify_Or_Err
     (T        : Boolean;
      Err      : out AIP.Err_T;
      Err_Type : AIP.Err_T) is
   begin
      if not T then
         Err := Err_Type;
      else
         Err := AIP.NOERR;
      end if;
   end Verify_Or_Err;

end AIP.Support;
