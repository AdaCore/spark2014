------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with Interfaces.C;
with System;

with GNAT.Source_Info;

package Assert is

   procedure Assertion_Failed
     (Message : String;
      File    : String   := GNAT.Source_Info.File;
      Line    : Positive := GNAT.Source_Info.Line);
   --  Display informational message including given source reference

   procedure C_Assertion_Failed
     (Message : System.Address;
      File    : System.Address;
      Line    : Interfaces.C.int);
   pragma Export (C, C_Assertion_Failed, "assertion_failed");
   --  Wrapper for the above, to be called from C code

end Assert;
