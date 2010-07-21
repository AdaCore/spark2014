------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Support is
   pragma Pure;

   procedure Verify (T : Boolean);

   procedure Verify_Or_Err
     (T        : Boolean;
      Err      : in out AIP.Err_T;
      Err_Type : AIP.Err_T);

end AIP.Support;
