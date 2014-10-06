------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--          F L O W _ U T I L I T Y . I N I T I A L I Z A T I O N           --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2014, Altran UK Limited                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

--  This package contains utilities related to the (default) initialization
--  of types and objects.

package Flow_Utility.Initialization is

   function Get_Default_Initialization (F : Flow_Id) return Node_Id;
   --  Get the default initialization expression for the given flow id
   --  (this only really works for record fields and direct mappings;
   --  magic strings are assumed to not be default initialized)

   function Is_Default_Initialized
     (F             : Flow_Id;
      Flow_Scop     : Flow_Scope;
      Explicit_Only : Boolean := False)
      return Boolean;
   --  As above, but can also return True if we can't actually get a node
   --  which is the default-initialized expression.

end Flow_Utility.Initialization;
