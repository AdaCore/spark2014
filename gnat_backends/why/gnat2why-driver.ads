------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - D R I V E R                       --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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
--  This package is the main driver for the Gnat2Why translation. It is
--  invoked by the gnat1 driver.
--
--  The main job of this package is to traverse the list of declarations of a
--  Gnat package, detect the kind of each declaration and dispatch to the
--  packages that deal with type declarations, data declarations and
--  function/procedure definitions.

with Types;     use Types;
with Why.Inter; use Why.Inter;

package Gnat2Why.Driver is

   Current_Why_Output_File : W_File_Sections;

   procedure GNAT_To_Why (GNAT_Root : Node_Id);
   --  Translates an entire GNAT tree for a compilation unit into
   --  a set of Why sources. This is the main driver for the
   --  Ada-to-Why back end and is invoked by Gnat1drv.

   function Is_Back_End_Switch (Switch : String) return Boolean;
   --  Returns True if and only if Switch denotes a back-end switch

   procedure Translate_Standard_Package;
   --  Translate the Ada Standard package

end Gnat2Why.Driver;
