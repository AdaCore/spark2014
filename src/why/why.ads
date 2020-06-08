------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                  W H Y                                   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package Why is
   pragma Pure;

   --  This package hierarchy provides a way to manipulate the syntax
   --  tree of a Why program and to generate some Why code out of it.

   Not_Implemented : exception;
   --  Use this exception for cases where an implementation is intended, but
   --  not done yet.

   Not_SPARK       : exception;
   --  Use this exception for cases that are outside the subset defined by
   --  SPARK.
   --  ??? this exception currently not used

   Unexpected_Node : exception;
   --  Use this exception for cases that are not expected at this place in the
   --  Ada AST.

end Why;
