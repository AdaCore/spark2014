------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y - A R G S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
--                       Copyright (C) 2017, Altran UK Limited              --
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

with Ada.Text_IO;               use Ada.Text_IO;
with GNAT.Directory_Operations; use GNAT.Directory_Operations;
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
   Flow_Advanced_Debug_Name     : constant String := "flow_advanced_debug";
   Flow_Generate_Contracts_Name : constant String :=
     "flow_generate_contracts";
   Flow_Termination_Name        : constant String := "flow_termination_proof";
   Flow_Show_GG_Name            : constant String := "flow_show_gg";
   Proof_Generate_Guards_Name   : constant String :=
     "proof_generate_axiom_guards";
   Limit_Subp_Name              : constant String := "limit_subp";
   Limit_Line_Name              : constant String := "limit_line";
   Pedantic_Name                : constant String := "pedantic";
   Ide_Mode_Name                : constant String := "ide_mode";
   Report_Mode_Name             : constant String := "report_mode";
   Why3_Args_Name               : constant String := "why3_args";
   Why3_Dir_Name                : constant String := "why3_dir";
   CP_Dir_Name                  : constant String := "codepeer_dir";

   ----------
   -- Init --
   ----------

   procedure Init (Filename : String) is

      function Get_Opt_Bool (V : JSON_Value; Field : String) return Boolean;
      --  return the boolean value of the Field [Field] of the JSON record [V].
      --  return False if the field doesn't exist.

      ------------------
      -- Get_Opt_Bool --
      ------------------

      function Get_Opt_Bool (V : JSON_Value; Field : String) return Boolean is
      begin
         return Has_Field (V, Field) and then Get (Get (V, Field));
      end Get_Opt_Bool;

      File_Text : Unbounded_String := Null_Unbounded_String;
      File      : File_Type;
      V         : JSON_Value;

   --  Start of processing for Init

   begin
      if Filename = "" then
         return;
      end if;
      Ada.Text_IO.Open (File, In_File, Filename);

      while not End_Of_File (File) loop
         Append (File_Text, Get_Line (File));
      end loop;
      V := Read (File_Text);
      Global_Gen_Mode         := Get_Opt_Bool (V, Global_Gen_Mode_Name);
      Check_Mode              := Get_Opt_Bool (V, Check_Mode_Name);
      Check_All_Mode          := Get_Opt_Bool (V, Check_All_Mode_Name);
      Flow_Analysis_Mode      := Get_Opt_Bool (V, Flow_Analysis_Mode_Name);
      Prove_Mode              := Get_Opt_Bool (V, Prove_Mode_Name);
      Debug_Mode              := Get_Opt_Bool (V, Debug_Mode_Name);
      Flow_Advanced_Debug     := Get_Opt_Bool (V, Flow_Advanced_Debug_Name);
      Flow_Generate_Contracts := Get_Opt_Bool (V,
                                               Flow_Generate_Contracts_Name);
      Flow_Termination_Proof  := Get_Opt_Bool (V, Flow_Termination_Name);
      Flow_Show_GG            := Get_Opt_Bool (V, Flow_Show_GG_Name);
      Proof_Generate_Guards   := Get_Opt_Bool (V, Proof_Generate_Guards_Name);
      Pedantic                := Get_Opt_Bool (V, Pedantic_Name);
      Ide_Mode                := Get_Opt_Bool (V, Ide_Mode_Name);
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
      if Has_Field (V, Why3_Args_Name) then
         declare
            Ar  : constant JSON_Array := Get (V, Why3_Args_Name);
         begin
            for Var_Index in Positive range 1 .. Length (Ar) loop
               Why3_Args.Append (Get (Get (Ar, Var_Index)));
            end loop;
         end;
      end if;
      if Has_Field (V, Why3_Dir_Name) then
         Why3_Dir := Get (Get (V, Why3_Dir_Name));
      end if;
      if Has_Field (V, CP_Dir_Name) then
         CP_Res_Dir := Get (Get (V, CP_Dir_Name));
      end if;
   end Init;

   ---------
   -- Set --
   ---------

   function Set (Obj_Dir : String) return String is

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
         Cur_Dir    : constant String := Get_Current_Dir;
      begin
         --  We need to switch to the given Obj_Dir so that the temp file is
         --  created there.

         Change_Dir (Obj_Dir);
         Create (FT, Name => File_Name);
         Put (FT, Write_Cont);

         Close (FT);
         Change_Dir (Cur_Dir);

         return Obj_Dir & File_Name;
      end Write_To_File;

      Obj : constant JSON_Value := Create_Object;

   --  Start of processing for Set

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
      Set_Field (Obj, Flow_Advanced_Debug_Name, Flow_Advanced_Debug);
      Set_Field (Obj, Flow_Generate_Contracts_Name, Flow_Generate_Contracts);
      Set_Field (Obj, Flow_Termination_Name, Flow_Termination_Proof);
      Set_Field (Obj, Flow_Show_GG_Name, Flow_Show_GG);
      Set_Field (Obj, Proof_Generate_Guards_Name, Proof_Generate_Guards);
      Set_Field (Obj, Pedantic_Name, Pedantic);
      Set_Field (Obj, Ide_Mode_Name, Ide_Mode);
      Set_Field (Obj, Report_Mode_Name, Report_Mode_Type'Image (Report_Mode));
      Set_Field (Obj, Limit_Subp_Name, Limit_Subp);
      Set_Field (Obj, Limit_Line_Name, Limit_Line);
      Set_Field (Obj, Why3_Dir_Name, Why3_Dir);
      Set_Field (Obj, CP_Dir_Name, CP_Res_Dir);
      declare
         A : JSON_Array := Empty_Array;
      begin
         for Arg of Why3_Args loop
            Append (A, Create (Arg));
         end loop;
         Set_Field (Obj, Why3_Args_Name, A);
      end;

      return Write_To_File (Obj);
   end Set;

end Gnat2Why_Args;
