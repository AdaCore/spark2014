------------------------------------------------------------------------------
--                                                                          --
--                            G N A T M E R G E                             --
--                                                                          --
--                        C O N F I G U R A T I O N                         --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2012-2014, AdaCore                  --
--                                                                          --
-- gnatmerge is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatmerge is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Directories;
with GNAT.Strings;
with GNATCOLL.Utils;    use GNATCOLL.Utils;

package Configuration is

   Prefix         : constant String := Executable_Location;
   Share_Dir      : constant String :=
                      Ada.Directories.Compose (Prefix, "share");
   Share_GM_Dir   : constant String :=
                      Ada.Directories.Compose (Share_Dir, "gnatmerge");
   Public_API     : constant String :=
                      Ada.Directories.Compose (Share_GM_Dir, "library");
   Plug_Ins       : constant String :=
                      Ada.Directories.Compose (Public_API, "plug-ins");
   Default_Script : aliased String :=
                      Ada.Directories.Compose (Public_API,
                                               "default_driver.py");

   User_Script    : aliased GNAT.Strings.String_Access :=
                      Default_Script'Access;
   Project_File   : aliased GNAT.Strings.String_Access := null;
   Run_Console    : aliased Boolean;
   Debug_Conf     : aliased GNAT.Strings.String_Access := null;

   procedure Read_Command_Line;

end Configuration;
