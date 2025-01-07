------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          G N A T 2 W H Y _ O P T S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2025, AdaCore                     --
--              Copyright (C) 2017-2025, Capgemini Engineering              --
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

   procedure Load (Args_File : String; Source_File : String) is

      function Get_Opt
        (V     : JSON_Value;
         Field : String)
         return Boolean
      is
        (Get (Get (V, Field)))
      with Pre => Has_Field (V, Field);
      --  Return the boolean value of the [Field] of the JSON record [V]

      function Get_Opt
        (V     : JSON_Value;
         Field : String)
         return Unbounded_String
      is
        (Get (Get (V, Field)))
      with Pre => Has_Field (V, Field);
      --  Return the string value of the [Field] of the JSON record [V]

      procedure Read_File_Specific_Info (V : JSON_Value);
      procedure Update_Warning_Status (V : JSON_Value);

      -----------------------------
      -- Read_File_Specific_Info --
      -----------------------------

      procedure Read_File_Specific_Info (V : JSON_Value) is
         R : constant JSON_Value :=
           (if Has_Field (V, Source_File)
            then Get (V, Source_File)
            else Get (V, "Ada"));

      begin
         No_Loop_Unrolling     := Get_Opt (R, No_Loop_Unrolling_Name);
         No_Inlining           := Get_Opt (R, No_Inlining_Name);
         Info_Messages         := Get_Opt (R, Info_Messages_Name);
         Check_Counterexamples := Get_Opt (R, Check_Counterexamples_Name);
         Mode                  := From_JSON (Get (R, GP_Mode_Name));

         if not Global_Gen_Mode then
            Proof_Warnings := Get_Opt (R, Proof_Warnings_Name);

            declare
               Ar : constant JSON_Array := Get (R, Why3_Args_Name);
            begin
               for Var_Index in Positive range 1 .. Length (Ar) loop
                  Why3_Args.Append (Get (Get (Ar, Var_Index)));
               end loop;
            end;
         end if;
         Update_Warning_Status (R);
      end Read_File_Specific_Info;

      procedure Update_Warning_Status (V : JSON_Value) is

         procedure Each_Kind (Field_Name : String;
                              New_Status : Warning_Enabled_Status);

         ---------------
         -- Each_Kind --
         ---------------

         procedure Each_Kind (Field_Name : String;
                              New_Status : Warning_Enabled_Status) is
            Ar : constant JSON_Array := Get (V, Field_Name);

         begin
            for Var_Index in Positive range 1 .. Length (Ar) loop
               declare
                  S : constant String := Get (Get (Ar, Var_Index));
               begin
                  for Kind in Misc_Warning_Kind loop
                     if Kind_Name (Kind) = S then
                        Warning_Status (Kind) := New_Status;
                     end if;
                  end loop;
               end;
            end loop;
         end Each_Kind;

      begin
         Each_Kind (Enabled_Warnings_Name, WS_Enabled);
         Each_Kind (Disabled_Warnings_Name, WS_Disabled);
         Each_Kind (Promoted_Warnings_Name, WS_Error);
      end Update_Warning_Status;

      V : constant JSON_Value := Read_File_Into_JSON (Args_File);

   --  Start of processing for Load

   begin
      Global_Gen_Mode         := Get_Opt (V, Global_Gen_Mode_Name);
      Output_Mode             :=
        Output_Mode_Type'Value (Get (Get (V, Output_Mode_Name)));
      Exclude_Line            := Get_Opt (V, Exclude_Line_Name);

      Debug_Exec_RAC          := Get_Opt (V, Debug_Exec_RAC_Name);
      Debug_Mode              := Get_Opt (V, Debug_Mode_Name);
      Flow_Advanced_Debug     := Get_Opt (V, Flow_Advanced_Debug_Name);
      Flow_Generate_Contracts := Get_Opt (V, Flow_Generate_Contracts_Name);

      if not Global_Gen_Mode then
         Limit_Units  := Get_Opt (V, Limit_Units_Name);
         Limit_Subp   := Get_Opt (V, Limit_Subp_Name);
         Limit_Region := Get_Opt (V, Limit_Region_Name);
         Limit_Name   := Get_Opt (V, Limit_Name_Name);

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

         Pedantic              := Get_Opt (V, Pedantic_Name);
         Flow_Show_GG          := Get_Opt (V, Flow_Show_GG_Name);
         Proof_Generate_Guards := Get_Opt (V, Proof_Generate_Guards_Name);
         Ide_Mode              := Get_Opt (V, Ide_Mode_Name);
         CWE                   := Get_Opt (V, CWE_Name);
         Parallel_Why3         := Get_Opt (V, Parallel_Why3_Name);

         Why3_Dir := Get_Opt (V, Why3_Dir_Name);
      end if;

      pragma Assert (Has_Field (V, File_Specific_Name));
      Read_File_Specific_Info (Get (V, File_Specific_Name));
   end Load;

end Gnat2Why_Opts.Reading;
