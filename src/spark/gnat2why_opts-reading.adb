------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y _ O P T S                       --
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

with Call;          use Call;
with GNATCOLL.JSON; use GNATCOLL.JSON;

package body Gnat2Why_Opts.Reading is

   ----------
   -- Load --
   ----------

   procedure Load (Args_File : String) is

      function Get_Opt (V : JSON_Value; Field : String) return Boolean
      is (Get (Get (V, Field)))
      with Pre => Has_Field (V, Field);
      --  Return the boolean value of the [Field] of the JSON record [V]

      function Get_Opt (V : JSON_Value; Field : String) return Integer
      is (Get (Get (V, Field)))
      with Pre => Has_Field (V, Field);
      --  Return the natural value of the [Field] of the JSON record [V]

      function Get_Opt (V : JSON_Value; Field : String) return Unbounded_String
      is (Get (Get (V, Field)))
      with Pre => Has_Field (V, Field);
      --  Return the string value of the [Field] of the JSON record [V]

      procedure Read_File_Specific_Info (V : JSON_Value);
      --  Read options only for this file
      procedure Read_Proof_Manifest (V : JSON_Value);
      --  Read the options provided by proof manifest

      -----------------------------
      -- Read_File_Specific_Info --
      -----------------------------

      procedure Read_File_Specific_Info (V : JSON_Value) is
      begin
         No_Loop_Unrolling := Get_Opt (V, No_Loop_Unrolling_Name);
         No_Inlining := Get_Opt (V, No_Inlining_Name);
         Check_Counterexamples := Get_Opt (V, Check_Counterexamples_Name);
         Mode := From_JSON (Get (V, GP_Mode_Name));

         if not Global_Gen_Mode then
            Proof_Warnings := Get_Opt (V, Proof_Warnings_Name);

            declare
               Ar : constant JSON_Array := Get (V, Why3_Args_Name);
            begin
               for Var_Index in Positive range 1 .. Length (Ar) loop
                  Why3_Args.Append (Get (Get (Ar, Var_Index)));
               end loop;
            end;
         end if;
         Warning_Status := VC_Kinds.From_JSON (Get (V, Warning_Status_Name));
      end Read_File_Specific_Info;

      -------------------------
      -- Read_Proof_Manifest --
      -------------------------

      procedure Read_Proof_Manifest (V : JSON_Value) is
         Ar : constant JSON_Array := Get (V, Proof_Manifest_Name);
      begin
         Proof_Manifest.Clear;

         for Var_Index in Positive range 1 .. Length (Ar) loop
            declare
               Obj    : constant JSON_Value := Get (Ar, Var_Index);
               Policy : Manifest_Subprogram;
            begin
               Policy.Path := Get_Opt (Obj, "path");

               if Has_Field (Obj, "file") then
                  Policy.File := Get_Opt (Obj, "file");
               end if;

               if Has_Field (Obj, "line") then
                  Policy.Line := Positive (Integer'(Get_Opt (Obj, "line")));
               end if;

               if Has_Field (Obj, "col") then
                  Policy.Column := Positive (Integer'(Get_Opt (Obj, "col")));
               end if;

               if Has_Field (Obj, "kind") then
                  Policy.Kind := Get_Opt (Obj, "kind");
               end if;

               if Has_Field (Obj, "profile") then
                  Policy.Profile := Get_Opt (Obj, "profile");
               end if;

               if Has_Field (Obj, "hierarchical") then
                  Policy.Hierarchical := Get_Opt (Obj, "hierarchical");
               end if;

               if Has_Field (Obj, "timeout") then
                  Policy.Timeout := Integer'(Get_Opt (Obj, "timeout"));
               end if;

               if Has_Field (Obj, "steps") then
                  Policy.Steps := Integer'(Get_Opt (Obj, "steps"));
               end if;

               if Has_Field (Obj, "memlimit") then
                  Policy.Memlimit := Integer'(Get_Opt (Obj, "memlimit"));
               end if;

               if Has_Field (Obj, "provers") then
                  declare
                     Provers : constant JSON_Array := Get (Obj, "provers");
                  begin
                     for Prover_Index in Positive range 1 .. Length (Provers)
                     loop
                        Policy.Provers.Append
                          (Get (Get (Provers, Prover_Index)));
                     end loop;
                  end;
               end if;

               Proof_Manifest.Append (Policy);
            end;
         end loop;
      end Read_Proof_Manifest;

      V : constant JSON_Value := Read_File_Into_JSON (Args_File);

   begin
      Global_Gen_Mode := Get_Opt (V, Global_Gen_Mode_Name);
      Output_Mode := Output_Mode_Type'Value (Get (Get (V, Output_Mode_Name)));
      Exclude_Line := Get_Opt (V, Exclude_Line_Name);

      Debug_Exec_RAC := Get_Opt (V, Debug_Exec_RAC_Name);
      Debug_Disable_Prover_Feedback :=
        Get_Opt (V, Debug_Disable_Prover_Feedback_Name);
      Debug_No_Cache_Output := Get_Opt (V, Debug_No_Cache_Output_Name);
      Debug_Mode := Get_Opt (V, Debug_Mode_Name);
      Flow_Advanced_Debug := Get_Opt (V, Flow_Advanced_Debug_Name);
      Flow_Generate_Contracts := Get_Opt (V, Flow_Generate_Contracts_Name);

      if not Global_Gen_Mode then
         Limit_Units := Get_Opt (V, Limit_Units_Name);
         Limit_Subp := Get_Opt (V, Limit_Subp_Name);
         Limit_Region := Get_Opt (V, Limit_Region_Name);
         Limit_Name := Get_Opt (V, Limit_Name_Name);
         Gnattest_Values := Get_Opt (V, Gnattest_Values_Name);

         declare
            Ar : constant JSON_Array := Get (V, Limit_Lines_Name);
         begin
            for Var_Index in Positive range 1 .. Length (Ar) loop
               Limit_Lines.Append (Get (Get (Ar, Var_Index)));
            end loop;
         end;

         Report_Mode :=
           Report_Mode_Type'Value (Get (Get (V, Report_Mode_Name)));

         Warning_Mode :=
           SPARK_Warning_Mode_Type'Value (Get (Get (V, Warning_Mode_Name)));

         Flow_Show_GG := Get_Opt (V, Flow_Show_GG_Name);
         Proof_Generate_Guards := Get_Opt (V, Proof_Generate_Guards_Name);
         Ide_Mode := Get_Opt (V, Ide_Mode_Name);
         CWE := Get_Opt (V, CWE_Name);
         Max_Why3_Processes := Get_Opt (V, Max_Why3_Processes_Name);
         Read_Proof_Manifest (V);

         Why3_Dir := Get_Opt (V, Why3_Dir_Name);
      end if;

      Read_File_Specific_Info (V);
   end Load;

end Gnat2Why_Opts.Reading;
