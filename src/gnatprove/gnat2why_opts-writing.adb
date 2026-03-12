------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ O P T S . W R I T I N G                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2026, AdaCore                     --
--              Copyright (C) 2017-2026, Capgemini Engineering              --
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

with Configuration;        use Configuration;
with Ada.Directories;      use Ada.Directories;
with Ada.Text_IO;          use Ada.Text_IO;
with GNATCOLL.JSON;        use GNATCOLL.JSON;
with GNATCOLL.Hash.Blake3; use GNATCOLL.Hash.Blake3;
with String_Utils;         use String_Utils;
with VC_Kinds;             use VC_Kinds;

package body Gnat2Why_Opts.Writing is

   -------------------
   -- Opt_File_Name --
   -------------------

   function Opt_File_Name
     (Translation_Phase : Boolean;
      Obj_Dir           : String;
      Why3_Dir          : String;
      Unit_Name         : String) return String
   is
      Hash_Context : Blake3_Context;
      File_Name    : String (1 .. 12);

      procedure Hash (Key : String; Value : String);
      procedure Hash (Key : String; Value : String_Lists.List);

      ----------
      -- Hash --
      ----------

      procedure Hash (Key : String; Value : String) is
      begin
         Update_Hash_Context
           (Hash_Context, Key & ASCII.NUL & Value & ASCII.NUL);
      end Hash;

      ----------
      -- Hash --
      ----------

      procedure Hash (Key : String; Value : String_Lists.List) is
      begin
         Update_Hash_Context (Hash_Context, Key & ASCII.NUL);
         for S of Value loop
            Update_Hash_Context (Hash_Context, S & ASCII.NUL);
         end loop;
      end Hash;

   begin
      Init_Hash_Context (Hash_Context);

      --  Hash fields in the same order and with the same conditionals as
      --  Pass_Extra_Options_To_Gnat2why calls Set_Field. Keep these two in
      --  sync when adding or removing options.

      Hash (Global_Gen_Mode_Name, Boolean'Image (not Translation_Phase));
      Hash (Output_Mode_Name, Gnat2Why_Opts.Output_Mode_Type'Image (Output));
      Hash (Exclude_Line_Name, CL_Switches.Exclude_Line.all);
      Hash (Gnattest_Values_Name, CL_Switches.Gnattest_Values.all);
      Hash (Debug_Exec_RAC_Name, Boolean'Image (Debug_Exec_RAC));
      Hash (Debug_Mode_Name, Boolean'Image (Debug));
      Hash (Flow_Advanced_Debug_Name, Boolean'Image (Flow_Extra_Debug));
      Hash
        (Flow_Generate_Contracts_Name,
         Boolean'Image (not CL_Switches.No_Global_Generation));

      --  Options needed only in phase 2

      if Translation_Phase then
         Hash (Limit_Units_Name, Boolean'Image (CL_Switches.U));
         Hash (Limit_Subp_Name, CL_Switches.Limit_Subp.all);
         Hash (Limit_Region_Name, CL_Switches.Limit_Region.all);
         Hash (Limit_Name_Name, CL_Switches.Limit_Name.all);
         Hash (Limit_Lines_Name, Limit_Lines);
         Hash
           (Report_Mode_Name, Gnat2Why_Opts.Report_Mode_Type'Image (Report));
         Hash
           (Warning_Mode_Name,
            Gnat2Why_Opts.SPARK_Warning_Mode_Type'Image (Warning_Mode));
         Hash (Flow_Show_GG_Name, Boolean'Image (CL_Switches.Flow_Show_GG));

         --  Mirror the if/else logic in Pass_Extra_Options_To_Gnat2why
         if CL_Switches.Function_Sandboxing.all = ""
           or else CL_Switches.Function_Sandboxing.all = "on"
         then
            Hash (Proof_Generate_Guards_Name, Boolean'Image (True));
         else
            Hash (Proof_Generate_Guards_Name, Boolean'Image (False));
         end if;

         Hash (Ide_Mode_Name, Boolean'Image (Configuration.IDE_Mode));
         Hash (CWE_Name, Boolean'Image (CL_Switches.CWE));
         Hash (Max_Why3_Processes_Name, Integer'Image (Max_Why3_Processes));
         Hash (Why3_Dir_Name, Ada.Directories.Full_Name (Why3_Dir));
      end if;

      --  File-specific options

      declare
         FS : Configuration.File_Specific renames
           Configuration.File_Specific_Map (Unit_Name);
      begin
         Hash
           (Check_Counterexamples_Name,
            Boolean'Image (FS.Check_Counterexamples));
         Hash (No_Loop_Unrolling_Name, Boolean'Image (FS.No_Loop_Unrolling));
         Hash (No_Inlining_Name, Boolean'Image (FS.No_Inlining));
         Hash (GP_Mode_Name, GP_Mode'Image (FS.Mode));

         --  Mirror To_JSON (W : Warning_Status_Array) in vc_kinds.adb:
         --  iterate Misc_Warning_Kind in declaration order.
         Update_Hash_Context (Hash_Context, Warning_Status_Name & ASCII.NUL);
         for MW in Misc_Warning_Kind loop
            Update_Hash_Context
              (Hash_Context,
               Misc_Warning_Kind'Image (MW)
               & "="
               & Warning_Enabled_Status'Image (FS.Warning_Status (MW))
               & ASCII.NUL);
         end loop;

         if Translation_Phase then
            Hash (Proof_Warnings_Name, Boolean'Image (FS.Proof_Warnings));
            Hash (Why3_Args_Name, Compute_Why3_Args (Obj_Dir, FS));
         end if;
      end;

      File_Name := Hash_Digest (Hash_Context) (1 .. 8) & ".tmp";
      return Compose (Obj_Dir, File_Name);
   end Opt_File_Name;

   ------------------------------------
   -- Pass_Extra_Options_To_Gnat2why --
   ------------------------------------

   function Pass_Extra_Options_To_Gnat2why
     (Translation_Phase : Boolean;
      Obj_Dir           : String;
      Why3_Dir          : String;
      Unit_Name         : String) return String
   is
      function To_JSON (SL : String_Lists.List) return JSON_Array;

      -------------
      -- To_JSON --
      -------------

      function To_JSON (SL : String_Lists.List) return JSON_Array is
         A : JSON_Array := GNATCOLL.JSON.Empty_Array;
      begin
         for S of SL loop
            Append (A, Create (S));
         end loop;
         return A;
      end To_JSON;

      Result : constant String :=
        Opt_File_Name (Translation_Phase, Obj_Dir, Why3_Dir, Unit_Name);

   begin
      --  Skip writing if a file with the same content hash already exists
      if Exists (Result) then
         return Result;
      end if;

      declare
         Obj         : constant JSON_Value := Create_Object;
         Output_File : File_Type;
      begin
         Set_Field (Obj, Global_Gen_Mode_Name, not Translation_Phase);
         Set_Field
           (Obj,
            Output_Mode_Name,
            Gnat2Why_Opts.Output_Mode_Type'Image (Output));
         Set_Field (Obj, Exclude_Line_Name, CL_Switches.Exclude_Line.all);
         Set_Field
           (Obj, Gnattest_Values_Name, CL_Switches.Gnattest_Values.all);

         --  Always store debug options

         Set_Field (Obj, Debug_Exec_RAC_Name, Debug_Exec_RAC);
         Set_Field (Obj, Debug_Mode_Name, Debug);
         Set_Field (Obj, Flow_Advanced_Debug_Name, Flow_Extra_Debug);
         Set_Field
           (Obj,
            Flow_Generate_Contracts_Name,
            not CL_Switches.No_Global_Generation);

         --  Options needed only in phase 2
         if Translation_Phase then
            Set_Field (Obj, Limit_Units_Name, CL_Switches.U);
            Set_Field (Obj, Limit_Subp_Name, CL_Switches.Limit_Subp.all);
            Set_Field (Obj, Limit_Region_Name, CL_Switches.Limit_Region.all);
            Set_Field (Obj, Limit_Name_Name, CL_Switches.Limit_Name.all);
            Set_Field (Obj, Limit_Lines_Name, To_JSON (Limit_Lines));

            Set_Field
              (Obj,
               Report_Mode_Name,
               Gnat2Why_Opts.Report_Mode_Type'Image (Report));

            Set_Field
              (Obj,
               Warning_Mode_Name,
               Gnat2Why_Opts.SPARK_Warning_Mode_Type'Image (Warning_Mode));

            Set_Field (Obj, Flow_Show_GG_Name, CL_Switches.Flow_Show_GG);

            if CL_Switches.Function_Sandboxing.all = ""
              or else CL_Switches.Function_Sandboxing.all = "on"
            then
               Set_Field (Obj, Proof_Generate_Guards_Name, True);
            else
               pragma Assert (CL_Switches.Function_Sandboxing.all = "off");
               Set_Field (Obj, Proof_Generate_Guards_Name, False);
            end if;

            Set_Field (Obj, Ide_Mode_Name, Configuration.IDE_Mode);
            Set_Field (Obj, CWE_Name, CL_Switches.CWE);
            Set_Field (Obj, Max_Why3_Processes_Name, Max_Why3_Processes);

            --  The call to Ada.Directories.Full_Name removes any trailing
            --  slash, which could confuse gnat2why.
            Set_Field
              (Obj, Why3_Dir_Name, Ada.Directories.Full_Name (Why3_Dir));
         end if;

         --  File-specific options (flattened to top level)

         declare
            FS : Configuration.File_Specific renames
              Configuration.File_Specific_Map (Unit_Name);
         begin
            Set_Field
              (Obj, Check_Counterexamples_Name, FS.Check_Counterexamples);
            Set_Field (Obj, No_Loop_Unrolling_Name, FS.No_Loop_Unrolling);
            Set_Field (Obj, No_Inlining_Name, FS.No_Inlining);
            Set_Field (Obj, GP_Mode_Name, To_JSON (FS.Mode));
            Set_Field (Obj, Warning_Status_Name, To_JSON (FS.Warning_Status));

            if Translation_Phase then
               Set_Field (Obj, Proof_Warnings_Name, FS.Proof_Warnings);

               Set_Field
                 (Obj,
                  Why3_Args_Name,
                  To_JSON (Compute_Why3_Args (Obj_Dir, FS)));
            end if;
         end;

         Create (Output_File, Name => Result);
         Put (Output_File, Write (Obj));
         Close (Output_File);
      end;

      return Result;
   end Pass_Extra_Options_To_Gnat2why;

end Gnat2Why_Opts.Writing;
