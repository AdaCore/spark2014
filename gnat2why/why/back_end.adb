------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             B A C K _ E N D                              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Adabkend;
with Namet;
with Opt;
with Stringt;
with System;

with Gnat2Why.Driver;
with Gnat2Why_Args;

package body Back_End is

   use Gnat2Why.Driver;

   package GNAT2Why_BE is new Adabkend
     (Product_Name       => "GNAT2WHY",
      Copyright_Years    => "2010-2011",
      Driver             => Gnat2Why.Driver.GNAT_To_Why,
      Is_Back_End_Switch => Gnat2Why.Driver.Is_Back_End_Switch);

   -------------------
   -- Call_Back_End --
   -------------------

   procedure Call_Back_End (Mode : Back_End_Mode_Type) is
      pragma Unreferenced (Mode);

      use type Opt.Warning_Mode_Type;
   begin
      --  If Global_Gen_Mode = True, ALI have been generated at this point,
      --  with suitable cross-reference section. Return now.

      if Gnat2Why_Args.Global_Gen_Mode then
         return;

      --  If Global_Gen_Mode = False, we run flow analysis and proof with
      --  warnings as set by the caller of gnat2why (default is that warnings
      --  are treated as errors).

      else
         --  Since the back end is called with all tables locked,
         --  first unlock any tables that we need to change.

         Namet.Unlock;
         Stringt.Unlock;

         --  Frontend warnings were suppressed in this mode. Change that to the
         --  expected warning mode for gnat2why.

         pragma Assert (Opt.Warning_Mode = Opt.Suppress);
         Opt.Warning_Mode := Gnat2Why_Args.Warning_Mode;

         GNAT2Why_BE.Call_Back_End;

         --  Make sure to lock any unlocked tables again before returning

         Namet.Lock;
         Stringt.Lock;
      end if;
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

      Gnat2Why_Args.Init;

      --  gnat2why is run in two main modes:
      --    Global_Gen_Mode = True for generating ALI files with effects.
      --    Global_Gen_Mode = False for flow analysis and proof.

      if Gnat2Why_Args.Global_Gen_Mode then
         --  In this mode, we should run the compiler with warnings as required
         --  by the user through switches -gnatw?

         null;

      else
         --  In this mode, we should run the frontend with no warnings, in
         --  order to avoid repeating those already issued, and then we should
         --  run flow analysis and proof with warnings-as-errors by default.

         Opt.Warning_Mode := Opt.Suppress;

         --  An ALI file should be generated only when generating globals.
         --  Otherwise, when translating the program to Why, ALI file
         --  generation should be disabled.

         Opt.Disable_ALI_File := True;
      end if;
   end Scan_Compiler_Arguments;

end Back_End;
