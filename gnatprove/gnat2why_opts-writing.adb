------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 G N A T 2 W H Y _ O P T S . W R I T I N G                --
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

with Configuration;              use Configuration;
with Ada.Directories;            use Ada.Directories;
with Ada.Text_IO;                use Ada.Text_IO;
with GNATCOLL.JSON;              use GNATCOLL.JSON;
with GNAT.SHA1;
with String_Utils;               use String_Utils;

package body Gnat2Why_Opts.Writing is

   ------------------------------------
   -- Pass_Extra_Options_To_Gnat2why --
   ------------------------------------

   function Pass_Extra_Options_To_Gnat2why
      (Translation_Phase : Boolean;
       Obj_Dir           : String;
       Proj_Name         : String) return String
   is
      function Write_To_File (V : JSON_Value) return String;
      --  Write a textual representation of V to file
      --  @return full name of the file that is to be passed to gnat2why using
      --    -gnates=<file>. The chosen file name will be identical for
      --    identical contents of the file.

      function To_JSON (SL : String_Lists.List) return JSON_Array;
      function To_JSON (FS : File_Specific) return JSON_Value;

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

      -------------
      -- To_JSON --
      -------------

      function To_JSON (FS : Configuration.File_Specific) return JSON_Value is
         Obj : constant JSON_Value := Create_Object;

      begin
         Set_Field (Obj, No_Loop_Unrolling_Name, FS.No_Loop_Unrolling);
         Set_Field (Obj, No_Inlining_Name,       FS.No_Inlining);
         Set_Field (Obj, Info_Messages_Name,     FS.Info);

         --  Why3_Args are only needed in phase 2; also Compute_Why3_Args
         --  might call gnatwhy3, which requires Write_Why3_Conf_File to be
         --  called, which happens just before this routine is called with
         --  Translation_Phase set to True.

         if Translation_Phase then
            Set_Field (Obj, Proof_Warnings_Name, FS.Proof_Warnings);

            Set_Field (Obj, Why3_Args_Name,
                       To_JSON (Compute_Why3_Args (Obj_Dir, FS)));
         end if;

         return Obj;
      end To_JSON;

      function To_JSON (SL : String_Lists.List) return JSON_Array is
         A : JSON_Array := GNATCOLL.JSON.Empty_Array;
      begin
         for S of SL loop
            Append (A, Create (S));
         end loop;
         return A;
      end To_JSON;

      --  Local variables

      Obj : constant JSON_Value := Create_Object;

   --  Start of processing for Pass_Extra_Options_To_Gnat2why

   begin
      Set_Field (Obj, Global_Gen_Mode_Name, not Translation_Phase);
      Set_Field (Obj, Check_Mode_Name, Configuration.Mode = GPM_Check);

      --  Always store debug options

      Set_Field (Obj, Debug_Mode_Name,          Debug);
      Set_Field (Obj, Flow_Advanced_Debug_Name, Flow_Extra_Debug);
      Set_Field (Obj, Flow_Generate_Contracts_Name,
                 not CL_Switches.No_Global_Generation);

      --  Options needed only in phase 2
      if Translation_Phase then
         Set_Field (Obj, Check_All_Mode_Name,
                    Configuration.Mode = GPM_Check_All);
         Set_Field (Obj, Flow_Analysis_Mode_Name,
                    Configuration.Mode = GPM_Flow);
         Set_Field (Obj, Prove_Mode_Name,
                    Configuration.Mode = GPM_Prove);

         Set_Field (Obj, Limit_Units_Name,  CL_Switches.U);
         Set_Field (Obj, Limit_Subp_Name,   CL_Switches.Limit_Subp.all);
         Set_Field (Obj, Limit_Line_Name,   CL_Switches.Limit_Line.all);
         Set_Field (Obj, Limit_Region_Name, CL_Switches.Limit_Region.all);

         Set_Field (Obj, Report_Mode_Name,
                    Gnat2Why_Opts.Report_Mode_Type'Image (Report));

         Set_Field (Obj,
                    Warning_Mode_Name,
                    Gnat2Why_Opts.SPARK_Warning_Mode_Type'Image
                      (Warning_Mode));

         Set_Field (Obj, Pedantic_Name,         CL_Switches.Pedantic);
         Set_Field (Obj, Flow_Termination_Name, CL_Switches.Flow_Termination);
         Set_Field (Obj, Flow_Show_GG_Name,     CL_Switches.Flow_Show_GG);
         Set_Field (Obj, Proof_Generate_Guards_Name,
                    not CL_Switches.No_Axiom_Guard);
         Set_Field (Obj, Debug_Trivial_Name,    CL_Switches.Debug_Trivial);
         Set_Field (Obj, Ide_Mode_Name,         Configuration.IDE_Mode);
         Set_Field (Obj, CWE_Name,              CL_Switches.CWE);

         Set_Field (Obj, Why3_Dir_Name, Obj_Dir);

         if CodePeer then
            Set_Field (Obj, CP_Dir_Name,
                       Compose
                         (Compose
                            (Compose (Obj_Dir, "codepeer"),
                             Base_Name (Proj_Name) & ".output"),
                          "sam"));
         end if;
      end if;

      --  File-specific options

      declare
         FS : constant JSON_Value := Create_Object;

      begin
         for FSC in Configuration.File_Specific_Map.Iterate loop
            declare
               File : String renames
                 Configuration.File_Specific_Maps.Key (FSC);
               Opts : Configuration.File_Specific renames
                 Configuration.File_Specific_Map (FSC);

            begin
               Set_Field (FS, File, To_JSON (Opts));
            end;
         end loop;

         Set_Field (Obj, File_Specific_Name, FS);
      end;

      return Write_To_File (Obj);
   end Pass_Extra_Options_To_Gnat2why;

end Gnat2Why_Opts.Writing;
