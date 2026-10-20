------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S P A R K _ T A R G E T                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2026-2026, AdaCore                     --
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

--  This package holds the name of the target that gnat2why analyzes code for.
--  It is set from the extra options that gnatprove passes to gnat2why, and it
--  is read by the SPARK-specific version of Sdefault, which the front end uses
--  to compute the value of attribute Target_Name. This indirection is needed
--  because Sdefault belongs to the front-end part of gnat2why, which cannot
--  depend on the units that read the extra options.

with Types; use Types;

package SPARK_Target is

   Target_Name : String_Ptr;
   --  Name of the target, with a trailing directory separator like in the
   --  front end. Null when gnatprove did not provide a target name, in which
   --  case a default value is used instead.

end SPARK_Target;
