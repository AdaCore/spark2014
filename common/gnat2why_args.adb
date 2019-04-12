------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y - A R G S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2019, AdaCore                     --
--                Copyright (C) 2017-2019, Altran UK Limited                --
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

with Ada.Directories;           use Ada.Directories;
with Ada.Text_IO;               use Ada.Text_IO;
with Call;                      use Call;
with GNAT.SHA1;
with GNATCOLL.JSON;             use GNATCOLL.JSON;

package body Gnat2Why_Args is

   --  The extra options are passed to gnat2why using a file, specified
   --  via -gnates. This file contains on each line a single argument.
   --  Each argument is of the form
   --    name=value
   --  where neither "name" nor "value" can contain spaces. Each "name"
   --  corresponds to a global variable in this package (lower case).

   --  For boolean variables, the presence of the name means "true", absence
   --  means "false". For other variables, the value is given after the "="
   --  sign. No "=value" part is allowed for boolean variables.

   Warning_Mode_Name            : constant String := "warning_mode";
   Global_Gen_Mode_Name         : constant String := "global_gen_mode";
   Check_Mode_Name              : constant String := "check_mode";
   Check_All_Mode_Name          : constant String := "check_all_mode";
   Flow_Analysis_Mode_Name      : constant String := "flow_analysis_mode";
   Prove_Mode_Name              : constant String := "prove_mode";
   Debug_Mode_Name              : constant String := "debug";
   Debug_Trivial_Name           : constant String := "debug_trivial";
   Flow_Advanced_Debug_Name     : constant String := "flow_advanced_debug";
   Flow_Generate_Contracts_Name : constant String :=
     "flow_generate_contracts";
   Flow_Termination_Name        : constant String := "flow_termination_proof";
   Flow_Show_GG_Name            : constant String := "flow_show_gg";
   Proof_Generate_Guards_Name   : constant String :=
     "proof_generate_axiom_guards";
   Proof_Warnings_Name          : constant String := "proof_warnings";
   Limit_Units_Name             : constant String := "limit_units";
   Limit_Subp_Name              : constant String := "limit_subp";
   Limit_Region_Name            : constant String := "limit_region";
   Limit_Line_Name              : constant String := "limit_line";
   Pedantic_Name                : constant String := "pedantic";
   No_Loop_Unrolling_Name       : constant String := "no_loop_unrolling";
   Ide_Mode_Name                : constant String := "ide_mode";
   Report_Mode_Name             : constant String := "report_mode";
   Why3_Args_Name               : constant String := "why3_args";
   Why3_Dir_Name                : constant String := "why3_dir";
   CP_Dir_Name                  : constant String := "codepeer_dir";
   CWE_Name                     : constant String := "cwe";
   No_Inlining_Name             : constant String := "no_inlining";
   Info_Messages_Name           : constant String := "info_messages";
   File_Specific_Name           : constant String := "file_specific";

   function To_JSON (L : String_Lists.List) return JSON_Array;
   function To_JSON (R : File_Specific) return JSON_Value;

   ----------
   -- Load --
   ----------

   procedure Load (Args_File   : String;
                   Source_File : String)
   is

      function Get_Opt_Bool (V : JSON_Value; Field : String) return Boolean;
      --  return the boolean value of the Field [Field] of the JSON record [V].
      --  return False if the field doesn't exist.

      procedure Read_File_Specific_Info (V : JSON_Value);

      ------------------
      -- Get_Opt_Bool --
      ------------------

      function Get_Opt_Bool (V : JSON_Value; Field : String) return Boolean is
      begin
         return Has_Field (V, Field) and then Get (Get (V, Field));
      end Get_Opt_Bool;

      -----------------------------
      -- Read_File_Specific_Info --
      -----------------------------

      procedure Read_File_Specific_Info (V : JSON_Value) is
         R : JSON_Value;
      begin
         if Has_Field (V, Source_File) then
            R := Get (V, Source_File);
         elsif Has_Field (V, "Ada") then
            R := Get (V, "Ada");
         else
            raise Program_Error;
         end if;
         Local_Proof_Warnings := Get_Opt_Bool (R, Proof_Warnings_Name);
         Local_No_Loop_Unrolling :=
           Get_Opt_Bool (R, No_Loop_Unrolling_Name);
         Local_No_Inlining := Get_Opt_Bool (R, No_Inlining_Name);
         Local_Info_Messages := Get_Opt_Bool (R, Info_Messages_Name);
         if Has_Field (R, Why3_Args_Name) then
            declare
               Ar : constant JSON_Array := Get (R, Why3_Args_Name);
            begin
               for Var_Index in Positive range 1 .. Length (Ar) loop
                  Local_Why3_Args.Append (Get (Get (Ar, Var_Index)));
               end loop;
            end;
         end if;
      end Read_File_Specific_Info;

      V : constant JSON_Value := Read_File_Into_JSON (Args_File);

   --  Start of processing for Load

   begin
      Global_Gen_Mode         := Get_Opt_Bool (V, Global_Gen_Mode_Name);
      Check_Mode              := Get_Opt_Bool (V, Check_Mode_Name);
      Check_All_Mode          := Get_Opt_Bool (V, Check_All_Mode_Name);
      Flow_Analysis_Mode      := Get_Opt_Bool (V, Flow_Analysis_Mode_Name);
      Prove_Mode              := Get_Opt_Bool (V, Prove_Mode_Name);
      Debug_Mode              := Get_Opt_Bool (V, Debug_Mode_Name);
      Debug_Trivial           := Get_Opt_Bool (V, Debug_Trivial_Name);
      Flow_Advanced_Debug     := Get_Opt_Bool (V, Flow_Advanced_Debug_Name);
      Flow_Generate_Contracts := Get_Opt_Bool (V,
                                               Flow_Generate_Contracts_Name);
      Flow_Termination_Proof  := Get_Opt_Bool (V, Flow_Termination_Name);
      Flow_Show_GG            := Get_Opt_Bool (V, Flow_Show_GG_Name);
      Proof_Generate_Guards   := Get_Opt_Bool (V, Proof_Generate_Guards_Name);
      Pedantic                := Get_Opt_Bool (V, Pedantic_Name);
      Ide_Mode                := Get_Opt_Bool (V, Ide_Mode_Name);
      CWE                     := Get_Opt_Bool (V, CWE_Name);
      Limit_Units             := Get_Opt_Bool (V, Limit_Units_Name);

      if Has_Field (V, Report_Mode_Name) then
         Report_Mode :=
           Report_Mode_Type'Value (Get (Get (V, Report_Mode_Name)));
      end if;
      if Has_Field (V, Warning_Mode_Name) then
         Warning_Mode :=
           SPARK_Warning_Mode_Type'Value (Get (Get (V, Warning_Mode_Name)));
      end if;
      if Has_Field (V, Limit_Subp_Name) then
         Limit_Subp := Get (Get (V, Limit_Subp_Name));
      end if;
      if Has_Field (V, Limit_Line_Name) then
         Limit_Line := Get (Get (V, Limit_Line_Name));
      end if;
      if Has_Field (V, Limit_Region_Name) then
         Limit_Region := Get (Get (V, Limit_Region_Name));
      end if;
      if Has_Field (V, Why3_Dir_Name) then
         Why3_Dir := Get (Get (V, Why3_Dir_Name));
      end if;
      if Has_Field (V, CP_Dir_Name) then
         CP_Res_Dir := Get (Get (V, CP_Dir_Name));
      end if;
      if Has_Field (V, File_Specific_Name) then
         Read_File_Specific_Info (Get (V, File_Specific_Name));
      end if;
   end Load;

   -----------
   -- Store --
   -----------

   function Store (Obj_Dir : String) return String is

      function Write_To_File (V : JSON_Value) return String;
      --  Write the Content string to a file and return the filename

      -------------------
      -- Write_To_File --
      -------------------

      function Write_To_File (V : JSON_Value) return String is
         Write_Cont : constant String := Write (V);
         File_Name  : constant String (1 .. 12) :=
           GNAT.SHA1.Digest (Write_Cont) (1 .. 8) & ".tmp";
         FT         : File_Type;
         Cur_Dir    : constant String := Current_Directory;
      begin
         --  We need to switch to the given Obj_Dir so that the temp file is
         --  created there.

         Set_Directory (Obj_Dir);
         Create (FT, Name => File_Name);
         Put (FT, Write_Cont);

         Close (FT);
         Set_Directory (Cur_Dir);

         return Compose (Obj_Dir, File_Name);
      end Write_To_File;

      Obj : constant JSON_Value := Create_Object;

   --  Start of processing for Store

   begin
      --  Warning_Mode is only relevant when Global_Mode = False, so ignore its
      --  value if Global_Mode = True.

      if not Global_Gen_Mode then
         Set_Field (Obj,
                    Warning_Mode_Name,
                    SPARK_Warning_Mode_Type'Image (Warning_Mode));
      end if;

      Set_Field (Obj, Global_Gen_Mode_Name, Global_Gen_Mode);
      Set_Field (Obj, Check_Mode_Name, Check_Mode);
      Set_Field (Obj, Check_All_Mode_Name, Check_All_Mode);
      Set_Field (Obj, Flow_Analysis_Mode_Name, Flow_Analysis_Mode);
      Set_Field (Obj, Prove_Mode_Name, Prove_Mode);
      Set_Field (Obj, Debug_Mode_Name, Debug_Mode);
      Set_Field (Obj, Debug_Trivial_Name, Debug_Trivial);
      Set_Field (Obj, Flow_Advanced_Debug_Name, Flow_Advanced_Debug);
      Set_Field (Obj, Flow_Generate_Contracts_Name, Flow_Generate_Contracts);
      Set_Field (Obj, Flow_Termination_Name, Flow_Termination_Proof);
      Set_Field (Obj, Flow_Show_GG_Name, Flow_Show_GG);
      Set_Field (Obj, Proof_Generate_Guards_Name, Proof_Generate_Guards);
      Set_Field (Obj, Pedantic_Name, Pedantic);
      Set_Field (Obj, Ide_Mode_Name, Ide_Mode);
      Set_Field (Obj, Report_Mode_Name, Report_Mode_Type'Image (Report_Mode));
      Set_Field (Obj, Limit_Units_Name, Limit_Units);
      Set_Field (Obj, Limit_Subp_Name, Limit_Subp);
      Set_Field (Obj, Limit_Region_Name, Limit_Region);
      Set_Field (Obj, Limit_Line_Name, Limit_Line);
      Set_Field (Obj, Why3_Dir_Name, Why3_Dir);
      Set_Field (Obj, CP_Dir_Name, CP_Res_Dir);
      Set_Field (Obj, CWE_Name, CWE);

      declare
         FS : constant JSON_Value := Create_Object;
         use File_Specific_Maps;
      begin
         for C in File_Specific_Map.Iterate loop
            declare
               File : String renames Key (C);
               Opts : File_Specific renames File_Specific_Map (C);
            begin
               Set_Field (FS, File, To_JSON (Opts));
            end;
         end loop;
         Set_Field (Obj, File_Specific_Name, FS);
      end;

      return Write_To_File (Obj);
   end Store;

   -------------
   -- To_JSON --
   -------------

   function To_JSON (R : File_Specific) return JSON_Value
   is
      Obj : constant JSON_Value := Create_Object;
   begin
      Set_Field (Obj, Proof_Warnings_Name, R.Proof_Warnings);
      Set_Field (Obj, No_Loop_Unrolling_Name, R.No_Loop_Unrolling);
      Set_Field (Obj, No_Inlining_Name, R.No_Inlining);
      Set_Field (Obj, Info_Messages_Name, R.Info_Messages);
      Set_Field (Obj, Why3_Args_Name, To_JSON (R.Why3_Args));
      return Obj;
   end To_JSON;

   function To_JSON (L : String_Lists.List) return JSON_Array
   is
      A : JSON_Array := Empty_Array;
   begin
      for Arg of L loop
         Append (A, Create (Arg));
      end loop;
      return A;
   end To_JSON;

end Gnat2Why_Args;
