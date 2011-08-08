------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                          A L T E R G O _ W R A P                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
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
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Directories;
with Ada.Text_IO;
with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.Expect;       use GNAT.Expect;
with GNAT.OS_Lib;       use GNAT.OS_Lib;

with Call;              use Call;
with String_Utils;      use String_Utils;

procedure Altergo_Wrap is

   Config       : Command_Line_Configuration;
   Verbose      : aliased Boolean := False;
   Timeout      : aliased Integer := 10;
   Steps        : aliased Integer := 0;

   procedure Call_AltErgo_On_File
     (File        : String;
      Result_File : String;
      Verbose     : Boolean := False);
   --  Call Altergo on a single File. Produce a file containing the result of
   --  the run with name Result_File. Don't take more time than the given
   --  Timeout in seconds. If the return value is "True", the VC has been
   --  proven, otherwise some error (timeout etc) was detected.

   function Read_Command_Line return String;
   --  Read Command Line and initialize variables; return the first argument
   --  and assume that it is a filename.

   --------------------------
   -- Call_AltErgo_On_File --
   --------------------------

   procedure Call_AltErgo_On_File
     (File        : String;
      Result_File : String;
      Verbose     : Boolean := False)
   is
      Command   : String_Access;
      Arguments : constant Argument_List :=
         (1 => new String'(Int_Image (Timeout)),
          2 => new String'("alt-ergo"),
          3 => new String'(File));
      Status : aliased Integer;
   begin
      if Verbose then
         Ada.Text_IO.Put_Line ("calling Alt-ergo on " & File);
      end if;

      declare
         Real_Args : constant Argument_List :=
            (if Steps /= 0 then
               Arguments &
                  (1 => new String'("-steps"),
                   2 => new String'(Int_Image (Steps)))
             else
                Arguments);
         S : constant String :=
            GNAT.Expect.Get_Command_Output
              (Command   => "why-cpulimit",
               Arguments => Real_Args,
               Input     => "",
               Status    => Status'Access,
               Err_To_Out => True);
         FT      : Ada.Text_IO.File_Type;
      begin
         Ada.Text_IO.Create (FT, Ada.Text_IO.Out_File, Result_File);

         if Status /= 0 or else S'Length = 0 then
            Ada.Text_IO.Put (FT, "File """);
            Ada.Text_IO.Put (FT, File);
            Ada.Text_IO.Put_Line (FT, """:Failure or Timeout");
         else
            Ada.Text_IO.Put (FT, S);
         end if;
         Ada.Text_IO.Close (FT);
      end;
      Free (Command);
   end Call_AltErgo_On_File;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   function Read_Command_Line return String is

   begin
      --  Install command line config
      Define_Switch (Config, Verbose'Access,
                     "-v", Long_Switch => "--verbose",
                     Help => "Output extra verbose information");

      Define_Switch (Config, Timeout'Access,
                     "-t=", Long_Switch => "--timeout=",
                     Default => 10,
                     Initial => 10,
                     Help =>
                        "Set the timeout in seconds (default is 10 seconds)");

      Define_Switch (Config, Steps'Access,
                     "-s=", Long_Switch => "--steps=",
                     Initial => 0,
                     Help => "Set the maximal number of prove steps");
      Getopt (Config);
      declare
         Filename : constant String := Get_Argument;
      begin
         if Filename'Length = 0 then
            Abort_With_Message ("No VC given, aborting.");
         end if;
         return Filename;
      end;

   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
   end Read_Command_Line;

   --  begin processing for Altergo_Wrap

   File_Argument : constant String := Read_Command_Line;
   Base_Of_VC    : constant String :=
      Ada.Directories.Base_Name (File_Argument);
   Result_File   : constant String := Base_Of_VC & ".rgo";
begin
   if Ends_With (File_Argument, "_ctx.why") then
      --  exit silently when given a context file
      GNAT.OS_Lib.OS_Exit (0);
   end if;
   Call_AltErgo_On_File (File_Argument, Result_File, Verbose);
end Altergo_Wrap;
