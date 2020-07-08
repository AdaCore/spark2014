------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             B A C K _ E N D                              --
--                                                                          --
--                                 B o d y                                  --
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

--  This is the Why target-dependent version of the Back_End package

with Ada.Directories;
with Adabkend;
with Debug; use Debug;
with Elists;
with Errout;
with Gnat2Why.Driver;
with Gnat2Why_Args;
with Gnat2Why_Opts;
with Namet;
with Opt;
with Osint;
with SPARK_Definition;
with System;

package body Back_End is

   package GNAT2Why_BE is new Adabkend
     (Product_Name       => "GNAT2WHY",
      Copyright_Years    => "2010-2020",
      Driver             => Gnat2Why.Driver.GNAT_To_Why,
      Is_Back_End_Switch => Gnat2Why.Driver.Is_Back_End_Switch);

   function To_Front_End_Warning_Mode
     (M : Gnat2Why_Opts.SPARK_Warning_Mode_Type)
      return Opt.Warning_Mode_Type;
   --  Transform warning mode type of gnat2why_args to the warning mode type of
   --  the front-end.

   -------------------
   -- Call_Back_End --
   -------------------

   procedure Call_Back_End (Mode : Back_End_Mode_Type) is
      pragma Unreferenced (Mode);

      Save_Warning_Mode : constant Opt.Warning_Mode_Type := Opt.Warning_Mode;
      --  Save original frontend warning mode for restoration before returning
      --  from Call_Back_End, as various checks which may issue warnings are
      --  performed after that.

   begin
      --  Since the back end is called with all tables locked, first unlock any
      --  tables that we need to change.

      Namet.Unlock;
      Elists.Unlock;

      --  gnat2why is run in two main modes:
      --    Global_Gen_Mode = True for generating ALI files with effects.
      --    Global_Gen_Mode = False for flow analysis and proof.

      --  Frontend warnings are issued when running in the second mode, and
      --  suppressed in the first mode to avoid issuing twice the same
      --  warnings. Change that setting in the second mode to the expected
      --  warning mode for flow analysis and proof.

      Errout.Finalize (Last_Call => False);
      if Errout.Compilation_Errors then
         goto Unlock;
      end if;
      Errout.Reset_Warnings;

      if not Gnat2Why_Args.Global_Gen_Mode then
         Opt.Warning_Mode :=
           To_Front_End_Warning_Mode (Gnat2Why_Args.Warning_Mode);
      end if;

      GNAT2Why_BE.Call_Back_End;

      Errout.Finalize (Last_Call => False);
      if Errout.Compilation_Errors then
         goto Unlock;
      end if;
      Errout.Reset_Warnings;

      --  Restore the original frontend warning mode

      if not Gnat2Why_Args.Global_Gen_Mode then
         Opt.Warning_Mode := Save_Warning_Mode;
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
         Args_File   : String renames
           Opt.SPARK_Switches_File_Name.all;
         Source_File : constant String :=
           Ada.Directories.Simple_Name (Osint.Get_First_Main_File_Name);
      begin
         Gnat2Why_Args.Load (Args_File, Source_File);
      end;

      --  gnat2why is run in two main modes:
      --    Global_Gen_Mode = True for generating ALI files with effects.
      --    Global_Gen_Mode = False for flow analysis and proof.

      if Gnat2Why_Args.Global_Gen_Mode then
         --  In this mode, we should run the compiler with warnings as required
         --  by the user through switches -gnatw?

         SPARK_Definition.Inhibit_Messages;

         --  In this mode, we should run the frontend with no warnings. They
         --  will be issued in the second run.

         Opt.Warning_Mode := Opt.Suppress;

      else
         --  An ALI file should be generated only when generating globals.
         --  Otherwise, when translating the program to Why, ALI file
         --  generation should be disabled.

         Opt.Disable_ALI_File := True;

         --  For the pretty output mode, we set -gnatdF to force alternative
         --  display of messages in Errout.

         if Gnat2Why_Args.Output_Mode = Gnat2Why_Opts.GPO_Pretty then
            Debug_Flag_FF := True;
         end if;
      end if;

      Debug_Flag_M := Gnat2Why_Args.No_Inlining;
      Debug_Flag_Underscore_F := Gnat2Why_Args.Info_Messages;

   end Scan_Compiler_Arguments;

   -------------------------------
   -- To_Front_End_Warning_Mode --
   -------------------------------

   function To_Front_End_Warning_Mode
     (M : Gnat2Why_Opts.SPARK_Warning_Mode_Type)
      return Opt.Warning_Mode_Type
   is
   begin
      return
        (case M is
            when Gnat2Why_Opts.SW_Suppress       => Opt.Suppress,
            when Gnat2Why_Opts.SW_Normal         => Opt.Normal,
            when Gnat2Why_Opts.SW_Treat_As_Error => Opt.Treat_As_Error);
   end To_Front_End_Warning_Mode;

end Back_End;
