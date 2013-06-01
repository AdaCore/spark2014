------------------------------------------------------------------------------
--                                                                          --
--                            G N A T M E R G E                             --
--                                                                          --
--                        C O N F I G U R A T I O N                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2012-2013, AdaCore                  --
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

with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.OS_Lib;       use GNAT.OS_Lib;
with Ada.Text_IO;       use Ada.Text_IO;

package body Configuration is

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line is
      Config : Command_Line_Configuration;

      procedure Abort_With_Help (Msg : String);

      ---------------------
      -- Abort_With_Help --
      ---------------------

      procedure Abort_With_Help (Msg : String) is
      begin
         Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
         Ada.Text_IO.New_Line;
         Display_Help (Config);
         GNAT.OS_Lib.OS_Exit (1);
      end Abort_With_Help;

   begin
      Define_Switch (Config,
                     User_Script'Access,
                     "-e:",
                     Long_Switch => "--execute=",
                     Argument    => "SCRIPT",
                     Help        => "Execute a python script");
      Define_Switch (Config,
                     Project_File'Access,
                     "-P:",
                     Argument    => "PROJECT",
                     Help        => "Load GNAT project file");
      Define_Switch (Config,
                     Run_Console'Access,
                     "-c",
                     "--console",
                     Help     => "Run the command-line interpreter");
      Define_Switch (Config,
                     Debug_Conf'Access,
                     "-d:",
                     Long_Switch => "--debug_conf=",
                     Argument    => "CONFIG_FILE",
                     Help        => "Load config file for debug traces");

      Getopt (Config);
   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
      when Invalid_Parameter =>
         Abort_With_Help ("No parameter given to switch -" & Full_Switch);
   end Read_Command_Line;

end Configuration;
