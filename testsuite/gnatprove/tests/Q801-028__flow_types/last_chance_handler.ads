------------------------------------------------------------------------------
--                                                                          --
--                             GNAT EXAMPLE                                 --
--                                                                          --
--          Copyright (C) 2014-2015, Free Software Foundation, Inc.         --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
--                                                                          --
--                                                                          --
--                                                                          --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

--  The "last chance handler" (LCH) is the routine automatically called when
--  any exception is propagated. It is not intended to be called directly. The
--  system-defined LCH simply stops the entire application, ungracefully.
--  Users may redefine it, however, as we have done here. This one turns off
--  all but the red LED, which it turns on, and then goes into an infinite
--  loop.

pragma SPARK_Mode (On);

with System;

package Last_Chance_Handler is

   procedure Last_Chance_Handler (Msg : in System.Address; Line : in Integer)
   with
       Global => null;


   pragma Export (C, Last_Chance_Handler, "__gnat_last_chance_handler");
   pragma No_Return (Last_Chance_Handler);
   pragma Weak_External (Last_Chance_Handler);

end Last_Chance_Handler;
