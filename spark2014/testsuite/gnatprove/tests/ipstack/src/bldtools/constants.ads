------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with System;
with System.Machine_Code; use System.Machine_Code;
with GNAT.Source_Info;

package Constants is
   generic
      Name : String;
      Val  : Integer;
   procedure CND;
end Constants;
