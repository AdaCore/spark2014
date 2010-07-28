------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

--# inherit AIP;

package AIP.Support is
   pragma Preelaborate;

   procedure Verify (T : Boolean);

   procedure Verify_Or_Err
     (T        : Boolean;
      Err      : out AIP.Err_T;
      Err_Type : AIP.Err_T);

   procedure Log (Msg : String);

end AIP.Support;
