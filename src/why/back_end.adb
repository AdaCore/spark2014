------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             B A C K _ E N D                              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
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

--  This is the Why target-dependent version of the Back_End package

with Ada.Directories;
with Adabkend;
with Debug; use Debug;
with Elists;
with Errout;
with Erroutc;
with Gnat2Why.Driver;
with Gnat2Why_Args;
with Gnat2Why_Opts;
with Namet;
with Opt;
with Osint;
with SPARK_Definition;
with System;
with VC_Kinds;

package body Back_End is

   package GNAT2Why_BE is new
     Adabkend
       (Product_Name       => "GNAT2WHY",
        Copyright_Years    => "2010-2025",
        Driver             => Gnat2Why.Driver.GNAT_To_Why,
        Is_Back_End_Switch => Gnat2Why.Driver.Is_Back_End_Switch);

   function To_Front_End_Warning_Mode
     (M : Gnat2Why_Opts.SPARK_Warning_Mode_Type) return Opt.Warning_Mode_Type;
   --  Transform warning mode type of gnat2why_args to the warning mode type of
   --  the front-end.

   -------------------
   -- Call_Back_End --
   -------------------

   procedure Call_Back_End (Mode : Back_End_Mode_Type) is
      pragma Unreferenced (Mode);
   begin
      --  Since the back end is called with all tables locked, first unlock any
      --  tables that we need to change.

      Namet.Unlock;
      Elists.Unlock;

      Errout.Finalize (Last_Call => False);
      if Errout.Compilation_Errors then
         goto Unlock;
      end if;

      GNAT2Why_BE.Call_Back_End;

      Errout.Finalize (Last_Call => False);
      if Errout.Compilation_Errors then
         goto Unlock;
      end if;

      <<Unlock>>
      --  Make sure to lock any unlocked tables again before returning

      Namet.Lock;
      Elists.Lock;
   end Call_Back_End;

   -------------------------------
   -- Gen_Or_Update_Object_File --
   -------------------------------

   procedure Gen_Or_Update_Object_File is
   begin
      null;
   end Gen_Or_Update_Object_File;

   -----------------------------
   -- Scan_Compiler_Arguments --
   -----------------------------

   procedure Scan_Compiler_Arguments is
      gnat_argv, save_argv : System.Address;
      pragma Import (C, gnat_argv, "gnat_argv");
      pragma Import (C, save_argv, "save_argv");

      gnat_argc, save_argc : Integer;
      pragma Import (C, gnat_argc, "gnat_argc");
      pragma Import (C, save_argc, "save_argc");

      use type System.Address;
      use type Gnat2Why_Opts.Output_Mode_Type;
      use type VC_Kinds.Warning_Enabled_Status;

   begin
      --  If save_argv is non null, it means we are part of gnat1+gnat2why
      --  and need to set gnat_argv to save_argv so that Ada.Command_Line
      --  has access to the command line.

      if save_argv /= System.Null_Address then
         gnat_argv := save_argv;
         gnat_argc := save_argc;
      end if;

      --  We are in the gnat2why executable, so GNATprove_Mode is always true
      --  note that this flag needs to be set very early on, since e.g.
      --  Scan_Compiler_Arguments uses it.

      Opt.GNATprove_Mode := True;

      GNAT2Why_BE.Scan_Compiler_Arguments;

      --  Read extra options for gnat2why

      declare
         Args_File   : String renames Opt.SPARK_Switches_File_Name.all;
         Source_File : constant String :=
           Ada.Directories.Simple_Name (Osint.Get_First_Main_File_Name);
      begin
         Gnat2Why_Args.Load (Args_File, Source_File);
      end;

      --  For the pretty output mode, we set -gnatdF to force alternative
      --  display of messages in Errout.

      if Gnat2Why_Args.Output_Mode in Gnat2Why_Opts.GPO_Pretty then
         Debug_Flag_FF := True;
      end if;

      --  For the colored output mode, we set the corresponding flag in
      --  Erroutc.

      if Gnat2Why_Args.Output_Mode = Gnat2Why_Opts.GPO_Pretty_Color then
         Erroutc.Use_SGR_Control := True;
      end if;

      --  gnat2why is run in two main modes:
      --    Global_Gen_Mode = True for generating ALI files with effects.
      --    Global_Gen_Mode = False for flow analysis and proof.

      if Gnat2Why_Args.Global_Gen_Mode then
         --  In this mode, we should run the frontend with no warnings. They
         --  will be issued in the second run.

         Opt.Warning_Mode := Opt.Suppress;

         --  In this mode, we should avoid issuing errors in marking. They will
         --  be issued in the second run.

         SPARK_Definition.Inhibit_Messages;

      else
         --  In this mode, we should run the frontend and gnat2why with warning
         --  mode specified through --warnings switch.

         Opt.Warning_Mode :=
           To_Front_End_Warning_Mode (Gnat2Why_Args.Warning_Mode);

         --  An ALI file should be generated only when generating globals.
         --  Otherwise, when translating the program to Why, ALI file
         --  generation should be disabled.

         Opt.Disable_ALI_File := True;
      end if;

      Debug_Flag_M := Gnat2Why_Args.No_Inlining;
      --  Make this depend on the value for the unrolling warnings
      Debug_Flag_Underscore_F :=
        VC_Kinds.Warning_Status (VC_Kinds.Warn_Info_Unrolling_Inlining)
        /= VC_Kinds.WS_Disabled;

   end Scan_Compiler_Arguments;

   -------------------------------
   -- To_Front_End_Warning_Mode --
   -------------------------------

   function To_Front_End_Warning_Mode
     (M : Gnat2Why_Opts.SPARK_Warning_Mode_Type) return Opt.Warning_Mode_Type
   is
   begin
      return
        (case M is
           when Gnat2Why_Opts.SW_Suppress       => Opt.Suppress,
           when Gnat2Why_Opts.SW_Normal         => Opt.Normal,
           when Gnat2Why_Opts.SW_Treat_As_Error => Opt.Treat_As_Error);
   end To_Front_End_Warning_Mode;

end Back_End;
