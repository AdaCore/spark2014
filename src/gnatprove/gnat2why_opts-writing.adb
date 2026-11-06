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

with Configuration;         use Configuration;
with Ada.Directories;       use Ada.Directories;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;           use Ada.Text_IO;
with GNATCOLL.JSON;         use GNATCOLL.JSON;
with GNATCOLL.Hash.Blake3;  use GNATCOLL.Hash.Blake3;
with String_Utils;          use String_Utils;
with VC_Kinds;              use VC_Kinds;

package body Gnat2Why_Opts.Writing is

   --  Complete effective options for one unit and phase. Keeping this value
   --  independent of Configuration lets both the filename and file contents
   --  be derived from the same snapshot.

   type Options is record
      Phase                         : Gnat2Why_Phase;
      Output                        : Output_Mode_Type;
      Exclude_Line                  : Unbounded_String;
      Target_Name                   : Unbounded_String;
      Gnattest_Values               : Unbounded_String;
      Debug_Exec_RAC                : Boolean;
      Debug_Disable_Prover_Feedback : Boolean;
      Debug_No_Cache_Output         : Boolean;
      Debug                         : Boolean;
      Flow_Extra_Debug              : Boolean;
      Flow_Generate_Contracts       : Boolean;
      Limit_Units                   : Boolean;
      Limit_Subp                    : Unbounded_String;
      Limit_Region                  : Unbounded_String;
      Limit_Name                    : Unbounded_String;
      Limit_Lines                   : String_Lists.List;
      Report                        : Report_Mode_Type;
      Warning_Mode                  : SPARK_Warning_Mode_Type;
      Flow_Show_GG                  : Boolean;
      Proof_Generate_Guards         : Boolean;
      IDE_Mode                      : Boolean;
      CWE                           : Boolean;
      Max_Why3_Processes            : Positive;
      Proof_Manifest                : Manifest_Subprogram_Vectors.Vector;
      Data_Rep_Files                : String_Lists.List;
      Why3_Dir                      : Unbounded_String;
      Check_Counterexamples         : Boolean;
      No_Loop_Unrolling             : Boolean;
      No_Inlining                   : Boolean;
      Mode                          : GP_Mode;
      Warning_Status                : Warning_Status_Array;
      Proof_Warnings                : Boolean;
      Why3_Args                     : String_Lists.List;
   end record;

   function Collect_Options
     (Phase           : Gnat2Why_Phase;
      Obj_Dir         : String;
      Why3_Dir        : String;
      Source_Path_Key : String;
      Proof_Manifest  : Manifest_Subprogram_Vectors.Vector;
      Data_Rep_Files  : String_Lists.List) return Options;
   --  Capture the effective settings for this unit and phase

   function Opt_File_Name (Obj_Dir : String; Opts : Options) return String;
   --  Derive the options filename from the captured settings

   ---------------------
   -- Collect_Options --
   ---------------------

   function Collect_Options
     (Phase           : Gnat2Why_Phase;
      Obj_Dir         : String;
      Why3_Dir        : String;
      Source_Path_Key : String;
      Proof_Manifest  : Manifest_Subprogram_Vectors.Vector;
      Data_Rep_Files  : String_Lists.List) return Options
   is
      FS : Configuration.File_Specific renames
        Configuration.File_Specific_Map (Source_Path_Key);
   begin
      pragma Assert (CL_Switches.Function_Sandboxing in "" | "on" | "off");

      return
        (Phase                         => Phase,
         Output                        => Output,
         Exclude_Line                  =>
           To_Unbounded_String (CL_Switches.Exclude_Line),
         Target_Name                   =>
           To_Unbounded_String (Configuration.Target_Name),
         Gnattest_Values               =>
           To_Unbounded_String (CL_Switches.Gnattest_Values),
         Debug_Exec_RAC                => Debug_Exec_RAC,
         Debug_Disable_Prover_Feedback =>
           CL_Switches.Debug_Disable_Prover_Feedback,
         Debug_No_Cache_Output         => CL_Switches.Debug_No_Cache_Output,
         Debug                         => Debug,
         Flow_Extra_Debug              => Flow_Extra_Debug,
         Flow_Generate_Contracts       => not CL_Switches.No_Global_Generation,
         Limit_Units                   => CL_Switches.U,
         Limit_Subp                    =>
           To_Unbounded_String (CL_Switches.Limit_Subp),
         Limit_Region                  =>
           To_Unbounded_String (CL_Switches.Limit_Region),
         Limit_Name                    =>
           To_Unbounded_String (CL_Switches.Limit_Name),
         Limit_Lines                   => Limit_Lines.all,
         Report                        => Report,
         Warning_Mode                  => Warning_Mode,
         Flow_Show_GG                  => CL_Switches.Flow_Show_GG,
         Proof_Generate_Guards         =>
           CL_Switches.Function_Sandboxing /= "off",
         IDE_Mode                      => Configuration.IDE_Mode,
         CWE                           => CL_Switches.CWE,
         Max_Why3_Processes            => Max_Why3_Processes,
         Proof_Manifest                => Proof_Manifest,
         Data_Rep_Files                => Data_Rep_Files,
         Why3_Dir                      =>
           (if Phase = Translation
            then To_Unbounded_String (Full_Name (Why3_Dir))
            else Null_Unbounded_String),
         Check_Counterexamples         => FS.Check_Counterexamples,
         No_Loop_Unrolling             => FS.No_Loop_Unrolling,
         No_Inlining                   => FS.No_Inlining,
         Mode                          => FS.Mode,
         Warning_Status                => FS.Warning_Status,
         Proof_Warnings                => FS.Proof_Warnings,
         Why3_Args                     =>
           (if Phase = Translation
            then Compute_Why3_Args (Obj_Dir, FS)
            else String_Lists.Empty_List));
   end Collect_Options;

   -------------------
   -- Opt_File_Name --
   -------------------

   function Opt_File_Name (Obj_Dir : String; Opts : Options) return String is
      Hash_Context : Blake3_Context;
      File_Name    : String (1 .. 12);

      procedure Hash (Key : String; Value : String);
      procedure Hash (Key : String; Value : String_Lists.List);
      procedure Hash
        (Key : String; Value : Manifest_Subprogram_Vectors.Vector);

      ----------
      -- Hash --
      ----------

      procedure Hash (Key : String; Value : String) is
      begin
         Update_Hash_Context
           (Hash_Context, Key & ASCII.NUL & Value & ASCII.NUL);
      end Hash;

      procedure Hash (Key : String; Value : String_Lists.List) is
      begin
         Update_Hash_Context (Hash_Context, Key & ASCII.NUL);
         for S of Value loop
            Update_Hash_Context (Hash_Context, S & ASCII.NUL);
         end loop;
      end Hash;

      procedure Hash (Key : String; Value : Manifest_Subprogram_Vectors.Vector)
      is
      begin
         --  Every field written for a policy has to be hashed here. A field
         --  that is written but not hashed lets two manifests that differ
         --  only in that field share an options file, so the second one
         --  silently reuses the settings of the first.

         Update_Hash_Context (Hash_Context, Key & ASCII.NUL);
         for Policy of Value loop
            Update_Hash_Context (Hash_Context, "subprogram" & ASCII.NUL);
            Hash ("id", Integer'Image (Policy.Id));
            Hash ("nested_in", Integer'Image (Policy.Nested_In));
            Hash ("path", To_String (Policy.Path));
            Hash ("kind", To_String (Policy.Kind));
            Hash ("profile", To_String (Policy.Profile));
            Hash ("hierarchical", Boolean'Image (Policy.Hierarchical));
            Hash ("file", To_String (Policy.File));
            Hash ("line", Integer'Image (Policy.Line));
            Hash ("col", Integer'Image (Policy.Column));
            Hash ("timeout", Integer'Image (Policy.Timeout));
            Hash ("steps", Integer'Image (Policy.Steps));
            Hash ("memlimit", Integer'Image (Policy.Memlimit));
            Hash ("provers", Policy.Provers);
         end loop;
      end Hash;

   begin
      Init_Hash_Context (Hash_Context);

      --  Preserve the hash order and representation used for existing files.
      --  Every option written below must be included here under the same phase
      --  condition, so different file contents cannot share a filename.

      Hash
        (Global_Gen_Mode_Name, Boolean'Image (Opts.Phase = Global_Generation));
      Hash (Output_Mode_Name, Output_Mode_Type'Image (Opts.Output));
      Hash (Exclude_Line_Name, To_String (Opts.Exclude_Line));
      Hash (Target_Name_Name, To_String (Opts.Target_Name));
      Hash (Gnattest_Values_Name, To_String (Opts.Gnattest_Values));
      Hash (Debug_Exec_RAC_Name, Boolean'Image (Opts.Debug_Exec_RAC));
      Hash
        (Debug_Disable_Prover_Feedback_Name,
         Boolean'Image (Opts.Debug_Disable_Prover_Feedback));
      Hash
        (Debug_No_Cache_Output_Name,
         Boolean'Image (Opts.Debug_No_Cache_Output));
      Hash (Debug_Mode_Name, Boolean'Image (Opts.Debug));
      Hash (Flow_Advanced_Debug_Name, Boolean'Image (Opts.Flow_Extra_Debug));
      Hash
        (Flow_Generate_Contracts_Name,
         Boolean'Image (Opts.Flow_Generate_Contracts));

      if Opts.Phase = Translation then
         Hash (Limit_Units_Name, Boolean'Image (Opts.Limit_Units));
         Hash (Limit_Subp_Name, To_String (Opts.Limit_Subp));
         Hash (Limit_Region_Name, To_String (Opts.Limit_Region));
         Hash (Limit_Name_Name, To_String (Opts.Limit_Name));
         Hash (Limit_Lines_Name, Opts.Limit_Lines);
         Hash (Report_Mode_Name, Report_Mode_Type'Image (Opts.Report));
         Hash
           (Warning_Mode_Name,
            SPARK_Warning_Mode_Type'Image (Opts.Warning_Mode));
         Hash (Flow_Show_GG_Name, Boolean'Image (Opts.Flow_Show_GG));
         Hash
           (Proof_Generate_Guards_Name,
            Boolean'Image (Opts.Proof_Generate_Guards));
         Hash (Ide_Mode_Name, Boolean'Image (Opts.IDE_Mode));
         Hash (CWE_Name, Boolean'Image (Opts.CWE));
         Hash
           (Max_Why3_Processes_Name, Integer'Image (Opts.Max_Why3_Processes));
         Hash (Proof_Manifest_Name, Opts.Proof_Manifest);
         Hash (Data_Rep_Files_Name, Opts.Data_Rep_Files);
         Hash (Why3_Dir_Name, To_String (Opts.Why3_Dir));
      end if;

      Hash
        (Check_Counterexamples_Name,
         Boolean'Image (Opts.Check_Counterexamples));
      Hash (No_Loop_Unrolling_Name, Boolean'Image (Opts.No_Loop_Unrolling));
      Hash (No_Inlining_Name, Boolean'Image (Opts.No_Inlining));
      Hash (GP_Mode_Name, GP_Mode'Image (Opts.Mode));

      --  Match the ordering used by To_JSON for warning statuses
      Update_Hash_Context (Hash_Context, Warning_Status_Name & ASCII.NUL);
      for MW in Misc_Warning_Kind loop
         Update_Hash_Context
           (Hash_Context,
            Misc_Warning_Kind'Image (MW)
            & "="
            & Warning_Enabled_Status'Image (Opts.Warning_Status (MW))
            & ASCII.NUL);
      end loop;

      if Opts.Phase = Translation then
         Hash (Proof_Warnings_Name, Boolean'Image (Opts.Proof_Warnings));
         Hash (Why3_Args_Name, Opts.Why3_Args);
      end if;

      File_Name := Hash_Digest (Hash_Context) (1 .. 8) & ".tmp";
      return Compose (Obj_Dir, File_Name);
   end Opt_File_Name;

   -------------------
   -- Opt_File_Name --
   -------------------

   function Opt_File_Name
     (Phase           : Gnat2Why_Phase;
      Obj_Dir         : String;
      Why3_Dir        : String;
      Source_Path_Key : String;
      Proof_Manifest  : Manifest_Subprogram_Vectors.Vector;
      Data_Rep_Files  : String_Utils.String_Lists.List) return String
   is
      Opts : constant Options :=
        Collect_Options
          (Phase,
           Obj_Dir,
           Why3_Dir,
           Source_Path_Key,
           Proof_Manifest,
           Data_Rep_Files);
   begin
      return Opt_File_Name (Obj_Dir, Opts);
   end Opt_File_Name;

   ------------------------------------
   -- Pass_Extra_Options_To_Gnat2why --
   ------------------------------------

   function Pass_Extra_Options_To_Gnat2why
     (Phase           : Gnat2Why_Phase;
      Obj_Dir         : String;
      Why3_Dir        : String;
      Source_Path_Key : String;
      Proof_Manifest  : Manifest_Subprogram_Vectors.Vector;
      Data_Rep_Files  : String_Utils.String_Lists.List) return String
   is
      function To_JSON (SL : String_Lists.List) return JSON_Array;
      function To_JSON
        (Policy : Manifest_Subprogram) return GNATCOLL.JSON.JSON_Value;
      function To_JSON
        (Entries : Manifest_Subprogram_Vectors.Vector) return JSON_Array;

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

      function To_JSON
        (Policy : Manifest_Subprogram) return GNATCOLL.JSON.JSON_Value
      is
         Obj : constant JSON_Value := Create_Object;
      begin
         Set_Field (Obj, "id", Policy.Id);
         Set_Field (Obj, "nested_in", Policy.Nested_In);
         Set_Field (Obj, "path", To_String (Policy.Path));
         Set_Field (Obj, "file", To_String (Policy.File));
         Set_Field (Obj, "line", Policy.Line);
         Set_Field (Obj, "col", Policy.Column);

         if Length (Policy.Kind) > 0 then
            Set_Field (Obj, "kind", To_String (Policy.Kind));
         end if;

         if Length (Policy.Profile) > 0 then
            Set_Field (Obj, "profile", To_String (Policy.Profile));
         end if;

         Set_Field (Obj, "hierarchical", Policy.Hierarchical);

         if Policy.Timeout /= Invalid_Manifest_Timeout then
            Set_Field (Obj, "timeout", Policy.Timeout);
         end if;

         if Policy.Steps /= Invalid_Manifest_Steps then
            Set_Field (Obj, "steps", Policy.Steps);
         end if;

         if Policy.Memlimit /= Invalid_Manifest_Memlimit then
            Set_Field (Obj, "memlimit", Policy.Memlimit);
         end if;

         if not Policy.Provers.Is_Empty then
            Set_Field (Obj, "provers", To_JSON (Policy.Provers));
         end if;

         return Obj;
      end To_JSON;

      function To_JSON
        (Entries : Manifest_Subprogram_Vectors.Vector) return JSON_Array
      is
         A : JSON_Array := GNATCOLL.JSON.Empty_Array;
      begin
         for Policy of Entries loop
            Append (A, To_JSON (Policy));
         end loop;
         return A;
      end To_JSON;

      Opts   : constant Options :=
        Collect_Options
          (Phase,
           Obj_Dir,
           Why3_Dir,
           Source_Path_Key,
           Proof_Manifest,
           Data_Rep_Files);
      Result : constant String := Opt_File_Name (Obj_Dir, Opts);

   begin
      --  Skip writing if a file with the same content hash already exists
      if Exists (Result) then
         return Result;
      end if;

      declare
         Obj         : constant JSON_Value := Create_Object;
         Output_File : File_Type;
      begin
         Set_Field (Obj, Global_Gen_Mode_Name, Opts.Phase = Global_Generation);
         Set_Field
           (Obj, Output_Mode_Name, Output_Mode_Type'Image (Opts.Output));
         Set_Field (Obj, Exclude_Line_Name, To_String (Opts.Exclude_Line));
         Set_Field (Obj, Target_Name_Name, To_String (Opts.Target_Name));
         Set_Field
           (Obj, Gnattest_Values_Name, To_String (Opts.Gnattest_Values));
         Set_Field (Obj, Debug_Exec_RAC_Name, Opts.Debug_Exec_RAC);
         Set_Field
           (Obj,
            Debug_Disable_Prover_Feedback_Name,
            Opts.Debug_Disable_Prover_Feedback);
         Set_Field
           (Obj, Debug_No_Cache_Output_Name, Opts.Debug_No_Cache_Output);
         Set_Field (Obj, Debug_Mode_Name, Opts.Debug);
         Set_Field (Obj, Flow_Advanced_Debug_Name, Opts.Flow_Extra_Debug);
         Set_Field
           (Obj, Flow_Generate_Contracts_Name, Opts.Flow_Generate_Contracts);

         if Opts.Phase = Translation then
            Set_Field (Obj, Limit_Units_Name, Opts.Limit_Units);
            Set_Field (Obj, Limit_Subp_Name, To_String (Opts.Limit_Subp));
            Set_Field (Obj, Limit_Region_Name, To_String (Opts.Limit_Region));
            Set_Field (Obj, Limit_Name_Name, To_String (Opts.Limit_Name));
            Set_Field (Obj, Limit_Lines_Name, To_JSON (Opts.Limit_Lines));
            Set_Field
              (Obj, Report_Mode_Name, Report_Mode_Type'Image (Opts.Report));
            Set_Field
              (Obj,
               Warning_Mode_Name,
               SPARK_Warning_Mode_Type'Image (Opts.Warning_Mode));
            Set_Field (Obj, Flow_Show_GG_Name, Opts.Flow_Show_GG);
            Set_Field
              (Obj, Proof_Generate_Guards_Name, Opts.Proof_Generate_Guards);
            Set_Field (Obj, Ide_Mode_Name, Opts.IDE_Mode);
            Set_Field (Obj, CWE_Name, Opts.CWE);
            Set_Field (Obj, Max_Why3_Processes_Name, Opts.Max_Why3_Processes);
            Set_Field
              (Obj, Proof_Manifest_Name, To_JSON (Opts.Proof_Manifest));
            Set_Field
              (Obj, Data_Rep_Files_Name, To_JSON (Opts.Data_Rep_Files));
            Set_Field (Obj, Why3_Dir_Name, To_String (Opts.Why3_Dir));
         end if;

         Set_Field
           (Obj, Check_Counterexamples_Name, Opts.Check_Counterexamples);
         Set_Field (Obj, No_Loop_Unrolling_Name, Opts.No_Loop_Unrolling);
         Set_Field (Obj, No_Inlining_Name, Opts.No_Inlining);
         Set_Field (Obj, GP_Mode_Name, To_JSON (Opts.Mode));
         Set_Field (Obj, Warning_Status_Name, To_JSON (Opts.Warning_Status));

         if Opts.Phase = Translation then
            Set_Field (Obj, Proof_Warnings_Name, Opts.Proof_Warnings);
            Set_Field (Obj, Why3_Args_Name, To_JSON (Opts.Why3_Args));
         end if;

         Create (Output_File, Name => Result);
         Put (Output_File, Write (Obj));
         Close (Output_File);
      end;

      return Result;
   end Pass_Extra_Options_To_Gnat2why;

end Gnat2Why_Opts.Writing;
